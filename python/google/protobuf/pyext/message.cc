// Protocol Buffers - Google's data interchange format
// Copyright 2008 Google Inc.  All rights reserved.
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

// Author: anuraag@google.com (Anuraag Agrawal)
// Author: tibell@google.com (Johan Tibell)

#include "google/protobuf/pyext/message.h"

#include <Python.h>
#include <structmember.h>  // A Python header file.

#include <climits>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "absl/base/optimization.h"
#include "absl/log/absl_check.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "google/protobuf/pyext/lazy_unique_ptr.h"

#ifndef PyVarObject_HEAD_INIT
#define PyVarObject_HEAD_INIT(type, size) PyObject_HEAD_INIT(type) size,
#endif
#ifndef Py_TYPE
#define Py_TYPE(ob) (((PyObject*)(ob))->ob_type)
#endif
#include "google/protobuf/descriptor.pb.h"
#include "absl/strings/escaping.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/io/coded_stream.h"
#include "google/protobuf/io/strtod.h"
#include "google/protobuf/io/zero_copy_stream_impl_lite.h"
#include "google/protobuf/map_field.h"
#include "google/protobuf/message.h"
#include "google/protobuf/text_format.h"
#include "google/protobuf/unknown_field_set.h"
#include "google/protobuf/util/message_differencer.h"
#include "google/protobuf/pyext/descriptor.h"
#include "google/protobuf/pyext/descriptor_pool.h"
#include "google/protobuf/pyext/extension_dict.h"
#include "google/protobuf/pyext/field.h"
#include "google/protobuf/pyext/map_container.h"
#include "google/protobuf/pyext/message_factory.h"
#include "google/protobuf/pyext/repeated_composite_container.h"
#include "google/protobuf/pyext/repeated_scalar_container.h"
#include "google/protobuf/pyext/safe_numerics.h"
#include "google/protobuf/pyext/scoped_pyobject_ptr.h"
#include "google/protobuf/pyext/unknown_field_set.h"

// clang-format off
#include "google/protobuf/port_def.inc"
// clang-format on

#define PyString_AsString(ob) \
  (PyUnicode_Check(ob) ? PyUnicode_AsUTF8(ob) : PyBytes_AsString(ob))
#define PyString_AsStringAndSize(ob, charpp, sizep)              \
  (PyUnicode_Check(ob)                                           \
       ? ((*(charpp) = const_cast<char*>(                        \
               PyUnicode_AsUTF8AndSize(ob, (sizep)))) == nullptr \
              ? -1                                               \
              : 0)                                               \
       : PyBytes_AsStringAndSize(ob, (charpp), (sizep)))

#define PROTOBUF_PYTHON_PUBLIC "google.protobuf"
#define PROTOBUF_PYTHON_INTERNAL "google.protobuf.internal"

namespace google {
namespace protobuf {
namespace python {

class MessageReflectionFriend {
 public:
  static void UnsafeShallowSwapFields(
      Message* lhs, Message* rhs,
      const std::vector<const FieldDescriptor*>& fields) {
    lhs->GetReflection()->UnsafeShallowSwapFields(lhs, rhs, fields);
  }
  static bool IsLazyField(const Reflection* reflection, const Message& message,
                          const FieldDescriptor* field) {
    return reflection->IsLazyField(field) ||
           reflection->IsLazyExtension(message, field);
  }
  static bool ContainsMapKey(const Reflection* reflection,
                             const Message& message,
                             const FieldDescriptor* field,
                             const MapKey& map_key) {
    return reflection->ContainsMapKey(message, field, map_key);
  }
};

static PyObject* kDESCRIPTOR;
static PyObject* kMessageFactory;
PyObject* EnumTypeWrapper_class;
static PyObject* PythonMessage_class;
static PyObject* kEmptyWeakref;
static PyObject* WKT_classes = nullptr;

namespace message_meta {

namespace {
// Copied over from internal 'google/protobuf/stubs/strutil.h'.
inline void LowerString(std::string* s) {
  std::string::iterator end = s->end();
  for (std::string::iterator i = s->begin(); i != end; ++i) {
    // tolower() changes based on locale.  We don't want this!
    if ('A' <= *i && *i <= 'Z') *i += 'a' - 'A';
  }
}
}  // namespace

// Finalize the creation of the Message class.
static int AddDescriptors(PyObject* cls, const Descriptor* descriptor) {
  // For each field set: cls.<field>_FIELD_NUMBER = <number>
  for (int i = 0; i < descriptor->field_count(); ++i) {
    const FieldDescriptor* field_descriptor = descriptor->field(i);
    ScopedPyObjectPtr property(NewFieldProperty(field_descriptor));
    if (property == nullptr) {
      return -1;
    }
    if (PyObject_SetAttrString(cls,
                               std::string(field_descriptor->name()).c_str(),
                               property.get()) < 0) {
      return -1;
    }
  }

  // For each enum set cls.<enum name> = EnumTypeWrapper(<enum descriptor>).
  for (int i = 0; i < descriptor->enum_type_count(); ++i) {
    const EnumDescriptor* enum_descriptor = descriptor->enum_type(i);
    ScopedPyObjectPtr enum_type(
        PyEnumDescriptor_FromDescriptor(enum_descriptor));
    if (enum_type == nullptr) {
      return -1;
    }
    // Add wrapped enum type to message class.
    ScopedPyObjectPtr wrapped(PyObject_CallFunctionObjArgs(
        EnumTypeWrapper_class, enum_type.get(), nullptr));
    if (wrapped == nullptr) {
      return -1;
    }
    if (PyObject_SetAttrString(cls,
                               std::string(enum_descriptor->name()).c_str(),
                               wrapped.get()) == -1) {
      return -1;
    }

    // For each enum value add cls.<name> = <number>
    for (int j = 0; j < enum_descriptor->value_count(); ++j) {
      const EnumValueDescriptor* enum_value_descriptor =
          enum_descriptor->value(j);
      ScopedPyObjectPtr value_number(
          PyLong_FromLong(enum_value_descriptor->number()));
      if (value_number == nullptr) {
        return -1;
      }
      if (PyObject_SetAttrString(
              cls, std::string(enum_value_descriptor->name()).c_str(),
              value_number.get()) == -1) {
        return -1;
      }
    }
  }

  // For each extension set cls.<extension name> = <extension descriptor>.
  //
  // Extension descriptors come from
  // <message descriptor>.extensions_by_name[name]
  // which was defined previously.
  for (int i = 0; i < descriptor->extension_count(); ++i) {
    const google::protobuf::FieldDescriptor* field = descriptor->extension(i);
    ScopedPyObjectPtr extension_field(PyFieldDescriptor_FromDescriptor(field));
    if (extension_field == nullptr) {
      return -1;
    }

    // Add the extension field to the message class.
    if (PyObject_SetAttrString(cls, std::string(field->name()).c_str(),
                               extension_field.get()) == -1) {
      return -1;
    }
  }

  return 0;
}

static PyObject* New(PyTypeObject* type, PyObject* args, PyObject* kwargs) {
  static const char* kwlist[] = {"name", "bases", "dict", nullptr};
  PyObject *bases, *dict;
  const char* name;

  // Check arguments: (name, bases, dict)
  if (!PyArg_ParseTupleAndKeywords(
          args, kwargs, "sO!O!:type", const_cast<char**>(kwlist), &name,
          &PyTuple_Type, &bases, &PyDict_Type, &dict)) {
    return nullptr;
  }

  // Check bases: only (), or (message.Message,) are allowed
  if (!(PyTuple_GET_SIZE(bases) == 0 ||
        (PyTuple_GET_SIZE(bases) == 1 &&
         PyTuple_GET_ITEM(bases, 0) == PythonMessage_class))) {
    PyErr_SetString(PyExc_TypeError,
                    "A Message class can only inherit from Message");
    return nullptr;
  }

  // Check dict['DESCRIPTOR']
  PyObject* py_descriptor = PyDict_GetItem(dict, kDESCRIPTOR);
  if (py_descriptor == nullptr) {
    PyErr_SetString(PyExc_TypeError, "Message class has no DESCRIPTOR");
    return nullptr;
  }
  if (!PyObject_TypeCheck(py_descriptor, &PyMessageDescriptor_Type)) {
    PyErr_Format(PyExc_TypeError, "Expected a message Descriptor, got %s",
                 py_descriptor->ob_type->tp_name);
    return nullptr;
  }
  const Descriptor* message_descriptor =
      PyMessageDescriptor_AsDescriptor(py_descriptor);
  if (message_descriptor == nullptr) {
    return nullptr;
  }

  // Messages have no __dict__
  ScopedPyObjectPtr slots(PyTuple_New(0));
  if (PyDict_SetItemString(dict, "__slots__", slots.get()) < 0) {
    return nullptr;
  }

  // Build the arguments to the base metaclass.
  // We change the __bases__ classes.
  ScopedPyObjectPtr new_args;

  if (WKT_classes == nullptr) {
    ScopedPyObjectPtr well_known_types(
        PyImport_ImportModule(PROTOBUF_PYTHON_INTERNAL ".well_known_types"));
    ABSL_DCHECK(well_known_types != nullptr);

    WKT_classes = PyObject_GetAttrString(well_known_types.get(), "WKTBASES");
    ABSL_DCHECK(WKT_classes != nullptr);
  }

  PyObject* well_known_class = PyDict_GetItemString(
      WKT_classes, std::string(message_descriptor->full_name()).c_str());
  if (well_known_class == nullptr) {
    new_args.reset(Py_BuildValue("s(OO)O", name, CMessage_Type,
                                 PythonMessage_class, dict));
  } else {
    new_args.reset(Py_BuildValue("s(OOO)O", name, CMessage_Type,
                                 PythonMessage_class, well_known_class, dict));
  }

  if (new_args == nullptr) {
    return nullptr;
  }
  // Call the base metaclass.
  ScopedPyObjectPtr result(PyType_Type.tp_new(type, new_args.get(), nullptr));
  if (result == nullptr) {
    return nullptr;
  }
  CMessageClass* newtype = reinterpret_cast<CMessageClass*>(result.get());

  // Cache the descriptor, both as Python object and as C++ pointer.
  const Descriptor* descriptor =
      PyMessageDescriptor_AsDescriptor(py_descriptor);
  if (descriptor == nullptr) {
    return nullptr;
  }
  Py_INCREF(py_descriptor);
  newtype->py_message_descriptor = py_descriptor;
  newtype->message_descriptor = descriptor;
  // TODO: Don't always use the canonical pool of the descriptor,
  // use the MessageFactory optionally passed in the class dict.
  PyDescriptorPool* py_descriptor_pool =
      GetDescriptorPool_FromPool(descriptor->file()->pool());
  if (py_descriptor_pool == nullptr) {
    return nullptr;
  }

  PyObject* py_message_factory_obj = PyDict_GetItem(dict, kMessageFactory);
  PyMessageFactory* py_message_factory = nullptr;
  if (py_message_factory_obj == nullptr) {
    py_message_factory = py_descriptor_pool->py_message_factory;
  } else {
    py_message_factory =
        reinterpret_cast<PyMessageFactory*>(py_message_factory_obj);
  }

  newtype->py_message_factory = py_message_factory;
  Py_INCREF(newtype->py_message_factory);

  // Register the message in the MessageFactory.
  // TODO: Move this call to MessageFactory.GetPrototype() when the
  // MessageFactory is fully implemented in C++.
  if (message_factory::RegisterMessageClass(newtype->py_message_factory,
                                            descriptor, newtype) < 0) {
    return nullptr;
  }

  // Continue with type initialization: add other descriptors, enum values...
  if (AddDescriptors(result.get(), descriptor) < 0) {
    return nullptr;
  }
  return result.release();
}

static void Dealloc(PyObject* pself) {
  CMessageClass* self = reinterpret_cast<CMessageClass*>(pself);
  Py_XDECREF(self->py_message_descriptor);
  Py_XDECREF(self->py_message_factory);
  return PyType_Type.tp_dealloc(pself);
}

static int GcTraverse(PyObject* pself, visitproc visit, void* arg) {
  CMessageClass* self = reinterpret_cast<CMessageClass*>(pself);
  Py_VISIT(self->py_message_descriptor);
  Py_VISIT(self->py_message_factory);
  return PyType_Type.tp_traverse(pself, visit, arg);
}

static int GcClear(PyObject* pself) {
  // It's important to keep the descriptor and factory alive, until the
  // C++ message is fully destructed.
  return PyType_Type.tp_clear(pself);
}

static PyGetSetDef Getters[] = {
    {nullptr},
};

// Compute some class attributes on the fly:
// - All the _FIELD_NUMBER attributes, for all fields and nested extensions.
// Returns a new reference, or NULL with an exception set.
static PyObject* GetClassAttribute(CMessageClass* self, PyObject* name) {
  char* attr;
  Py_ssize_t attr_size;
  static const char kSuffix[] = "_FIELD_NUMBER";
  if (PyString_AsStringAndSize(name, &attr, &attr_size) >= 0 &&
      absl::EndsWith(absl::string_view(attr, attr_size), kSuffix)) {
    std::string field_name(attr, attr_size - sizeof(kSuffix) + 1);
    LowerString(&field_name);

    // Try to find a field with the given name, without the suffix.
    const FieldDescriptor* field =
        self->message_descriptor->FindFieldByLowercaseName(field_name);
    if (!field) {
      // Search nested extensions as well.
      field =
          self->message_descriptor->FindExtensionByLowercaseName(field_name);
    }
    if (field) {
      return PyLong_FromLong(field->number());
    }
  }
  PyErr_SetObject(PyExc_AttributeError, name);
  return nullptr;
}

static PyObject* GetAttr(CMessageClass* self, PyObject* name) {
  PyObject* result = CMessageClass_Type->tp_base->tp_getattro(
      reinterpret_cast<PyObject*>(self), name);
  if (result != nullptr) {
    return result;
  }
  if (!PyErr_ExceptionMatches(PyExc_AttributeError)) {
    return nullptr;
  }

  PyErr_Clear();
  return GetClassAttribute(self, name);
}

}  // namespace message_meta

// Protobuf has a 64MB limit built in, this variable will override this. Please
// do not enable this unless you fully understand the implications: protobufs
// must all be kept in memory at the same time, so if they grow too big you may
// get OOM errors. The protobuf APIs do not provide any tools for processing
// protobufs in chunks.  If you have protos this big you should break them up if
// it is at all convenient to do so.
#ifdef PROTOBUF_PYTHON_ALLOW_OVERSIZE_PROTOS
static bool allow_oversize_protos = true;
#else
static bool allow_oversize_protos = false;
#endif

static PyTypeObject _CMessageClass_Type = {
    PyVarObject_HEAD_INIT(&PyType_Type, 0) FULL_MODULE_NAME
    ".MessageMeta",         // tp_name
    sizeof(CMessageClass),  // tp_basicsize
    0,                      // tp_itemsize
    message_meta::Dealloc,  // tp_dealloc
#if PY_VERSION_HEX < 0x03080000
    nullptr, /* tp_print */
#else
    0, /* tp_vectorcall_offset */
#endif
    nullptr,                              // tp_getattr
    nullptr,                              // tp_setattr
    nullptr,                              // tp_compare
    nullptr,                              // tp_repr
    nullptr,                              // tp_as_number
    nullptr,                              // tp_as_sequence
    nullptr,                              // tp_as_mapping
    nullptr,                              // tp_hash
    nullptr,                              // tp_call
    nullptr,                              // tp_str
    (getattrofunc)message_meta::GetAttr,  // tp_getattro
    nullptr,                              // tp_setattro
    nullptr,                              // tp_as_buffer
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE | Py_TPFLAGS_HAVE_GC,  // tp_flags
    "The metaclass of ProtocolMessages",                            // tp_doc
    message_meta::GcTraverse,  // tp_traverse
    message_meta::GcClear,     // tp_clear
    nullptr,                   // tp_richcompare
    0,                         // tp_weaklistoffset
    nullptr,                   // tp_iter
    nullptr,                   // tp_iternext
    nullptr,                   // tp_methods
    nullptr,                   // tp_members
    message_meta::Getters,     // tp_getset
    nullptr,                   // tp_base
    nullptr,                   // tp_dict
    nullptr,                   // tp_descr_get
    nullptr,                   // tp_descr_set
    0,                         // tp_dictoffset
    nullptr,                   // tp_init
    nullptr,                   // tp_alloc
    message_meta::New,         // tp_new
};
PyTypeObject* CMessageClass_Type = &_CMessageClass_Type;

static CMessageClass* CheckMessageClass(PyTypeObject* cls) {
  if (!PyObject_TypeCheck(cls, CMessageClass_Type)) {
    PyErr_Format(PyExc_TypeError, "Class %s is not a Message", cls->tp_name);
    return nullptr;
  }
  return reinterpret_cast<CMessageClass*>(cls);
}

static const Descriptor* GetMessageDescriptor(PyTypeObject* cls) {
  CMessageClass* type = CheckMessageClass(cls);
  if (type == nullptr) {
    return nullptr;
  }
  return type->message_descriptor;
}

// Forward declarations
namespace cmessage {
int InternalReleaseFieldByDescriptor(CMessage* self,
                                     const FieldDescriptor* field_descriptor);
}  // namespace cmessage

// ---------------------------------------------------------------------

PyObject* EncodeError_class;
PyObject* DecodeError_class;
PyObject* PickleError_class;

// Format an error message for unexpected types.
// Always return with an exception set.
void FormatTypeError(PyObject* arg, const char* expected_types) {
  // This function is often called with an exception set.
  // Clear it to call PyObject_Repr() in good conditions.
  PyErr_Clear();
  PyObject* repr = PyObject_Repr(arg);
  if (repr) {
    PyErr_Format(
        PyExc_TypeError, "%.100s has type %.100s, but expected one of: %s",
        PyString_AsString(repr), Py_TYPE(arg)->tp_name, expected_types);
    Py_DECREF(repr);
  }
}

void OutOfRangeError(PyObject* arg) {
  PyObject* s = PyObject_Str(arg);
  if (s) {
    PyErr_Format(PyExc_ValueError, "Value out of range: %s",
                 PyString_AsString(s));
    Py_DECREF(s);
  }
}

template <class RangeType, class ValueType>
bool VerifyIntegerCastAndRange(PyObject* arg, ValueType value) {
  if (ABSL_PREDICT_FALSE(value == -1 && PyErr_Occurred())) {
    if (PyErr_ExceptionMatches(PyExc_OverflowError)) {
      // Replace it with the same ValueError as pure python protos instead of
      // the default one.
      PyErr_Clear();
      OutOfRangeError(arg);
    }  // Otherwise propagate existing error.
    return false;
  }
  if (ABSL_PREDICT_FALSE(!IsValidNumericCast<RangeType>(value))) {
    OutOfRangeError(arg);
    return false;
  }
  return true;
}

template <class T>
bool CheckAndGetInteger(PyObject* arg, T* value) {
  // This effectively defines an integer as "an object that can be cast as
  // an integer and can be used as an ordinal number".
  // This definition includes everything with a valid __index__() implementation
  // and shouldn't cast the net too wide.
  if (!strcmp(Py_TYPE(arg)->tp_name, "numpy.ndarray") ||
      (!strcmp(Py_TYPE(arg)->tp_name, "bool")) ||
      ABSL_PREDICT_FALSE(!PyIndex_Check(arg))) {
    FormatTypeError(arg, "int");
    return false;
  }

  PyObject* arg_py_int = PyNumber_Index(arg);
  if (PyErr_Occurred()) {
    // Propagate existing error.
    return false;
  }

  if (std::numeric_limits<T>::min() == 0) {
    // Unsigned case.
    unsigned PY_LONG_LONG ulong_result = PyLong_AsUnsignedLongLong(arg_py_int);
    Py_DECREF(arg_py_int);
    if (VerifyIntegerCastAndRange<T, unsigned PY_LONG_LONG>(arg,
                                                            ulong_result)) {
      *value = static_cast<T>(ulong_result);
    } else {
      return false;
    }
  } else {
    // Signed case.
    Py_DECREF(arg_py_int);
    PY_LONG_LONG long_result = PyLong_AsLongLong(arg);
    if (VerifyIntegerCastAndRange<T, PY_LONG_LONG>(arg, long_result)) {
      *value = static_cast<T>(long_result);
    } else {
      return false;
    }
  }
  return true;
}

// These are referenced by repeated_scalar_container, and must
// be explicitly instantiated.
template bool CheckAndGetInteger<int32_t>(PyObject*, int32_t*);
template bool CheckAndGetInteger<int64_t>(PyObject*, int64_t*);
template bool CheckAndGetInteger<uint32_t>(PyObject*, uint32_t*);
template bool CheckAndGetInteger<uint64_t>(PyObject*, uint64_t*);

bool CheckAndGetDouble(PyObject* arg, double* value) {
  *value = PyFloat_AsDouble(arg);
  if (!strcmp(Py_TYPE(arg)->tp_name, "numpy.ndarray") ||
      ABSL_PREDICT_FALSE(*value == -1 && PyErr_Occurred())) {
    FormatTypeError(arg, "int, float");
    return false;
  }
  return true;
}

bool CheckAndGetFloat(PyObject* arg, float* value) {
  double double_value;
  if (!CheckAndGetDouble(arg, &double_value)) {
    return false;
  }
  *value = io::SafeDoubleToFloat(double_value);
  return true;
}

bool CheckAndGetBool(PyObject* arg, bool* value) {
  long long_value = PyLong_AsLong(arg);  // NOLINT
  if (long_value == -1 && PyErr_Occurred()) {
    // In NumPy 2.3, numpy.bool does not have an __index__ method and cannot
    // be converted to a long using PyLong_AsLong.
    if (!strcmp(Py_TYPE(arg)->tp_name, "numpy.bool")) {
      PyErr_Clear();
      int is_true = PyObject_IsTrue(arg);
      if (is_true >= 0) {
        *value = static_cast<bool>(is_true);
        return true;
      }
    }
    FormatTypeError(arg, "int, bool");
    return false;
  } else if (!strcmp(Py_TYPE(arg)->tp_name, "numpy.ndarray")) {
    FormatTypeError(arg, "int, bool");
    return false;
  }
  *value = static_cast<bool>(long_value);

  return true;
}

bool AllowInvalidUTF8(const FieldDescriptor* field) { return false; }

std::optional<absl::string_view> CheckString(
    PyObject* arg, const FieldDescriptor* descriptor) {
  ABSL_DCHECK(descriptor->type() == FieldDescriptor::TYPE_STRING ||
              descriptor->type() == FieldDescriptor::TYPE_BYTES);
  if (descriptor->type() == FieldDescriptor::TYPE_STRING) {
    if (PyUnicode_Check(arg)) {
      // Use the str object's cached UTF-8 representation — no allocation.
      // The pointer is valid as long as arg is alive.
      Py_ssize_t utf8_len;
      const char* utf8 = PyUnicode_AsUTF8AndSize(arg, &utf8_len);
      if (utf8 == nullptr) return std::nullopt;
      return absl::string_view(utf8, utf8_len);
    }
  }

  if (PyBytes_Check(arg)) {
    absl::string_view value(PyBytes_AS_STRING(arg), PyBytes_GET_SIZE(arg));
    if (descriptor->type() == FieldDescriptor::TYPE_STRING &&
        !AllowInvalidUTF8(descriptor)) {
      PyObject* unicode =
          PyUnicode_FromStringAndSize(value.data(), value.size());
      if (unicode == nullptr) {
        return std::nullopt;
      }
      Py_DECREF(unicode);
    }
    return value;
  }
      reflection->SetInt32(message, field_descriptor, value);
      break;
    }
    case FieldDescriptor::CPPTYPE_INT64: {
      PROTOBUF_CHECK_GET_INT64(arg, value, -1);
      reflection->SetInt64(message, field_descriptor, value);
      break;
    }
    case FieldDescriptor::CPPTYPE_UINT32: {
      PROTOBUF_CHECK_GET_UINT32(arg, value, -1);
      reflection->SetUInt32(message, field_descriptor, value);
      break;
    }
    case FieldDescriptor::CPPTYPE_UINT64: {
      PROTOBUF_CHECK_GET_UINT64(arg, value, -1);
      reflection->SetUInt64(message, field_descriptor, value);
      break;
    }
    case FieldDescriptor::CPPTYPE_FLOAT: {
      PROTOBUF_CHECK_GET_FLOAT(arg, value, -1);
      reflection->SetFloat(message, field_descriptor, value);
      break;
    }
    case FieldDescriptor::CPPTYPE_DOUBLE: {
      PROTOBUF_CHECK_GET_DOUBLE(arg, value, -1);
      reflection->SetDouble(message, field_descriptor, value);
      break;
    }
    case FieldDescriptor::CPPTYPE_BOOL: {
      PROTOBUF_CHECK_GET_BOOL(arg, value, -1);
      reflection->SetBool(message, field_descriptor, value);
      break;
    }
    case FieldDescriptor::CPPTYPE_STRING: {
      if (!CheckAndSetString(arg, message, field_descriptor, reflection, false,
                             -1)) {
        return -1;
      }
      break;
    }
    case FieldDescriptor::CPPTYPE_ENUM: {
      PROTOBUF_CHECK_GET_INT32(arg, value, -1);
      if (!field_descriptor->legacy_enum_field_treated_as_closed()) {
        reflection->SetEnumValue(message, field_descriptor, value);
      } else {
        const EnumDescriptor* enum_descriptor = field_descriptor->enum_type();
        const EnumValueDescriptor* enum_value =
            enum_descriptor->FindValueByNumber(value);
        if (enum_value != nullptr) {
          reflection->SetEnum(message, field_descriptor, enum_value);
        } else {
          PyErr_Format(PyExc_ValueError, "Unknown enum value: %d", value);
          return -1;
        }
      }
      break;
    }
    default:
      PyErr_Format(PyExc_SystemError,
                   "Setting value to a field of unknown type %d",
                   field_descriptor->cpp_type());
      return -1;
  }

  return 0;
}

int InternalSetScalar(CMessage* self, const FieldDescriptor* field_descriptor,
                      PyObject* arg) {
  if (!CheckFieldBelongsToMessage(field_descriptor, self->message)) {
    return -1;
  }

  if (MaybeReleaseOverlappingOneofField(self, field_descriptor) < 0) {
    return -1;
  }

  return InternalSetNonOneofScalar(self->message, field_descriptor, arg);
}

PyObject* FromString(PyTypeObject* cls, PyObject* serialized) {
  PyObject* py_cmsg =
      PyObject_CallObject(reinterpret_cast<PyObject*>(cls), nullptr);
  if (py_cmsg == nullptr) {
    return nullptr;
  }
  CMessage* cmsg = reinterpret_cast<CMessage*>(py_cmsg);

  ScopedPyObjectPtr py_length(MergeFromString(cmsg, serialized));
  if (py_length == nullptr) {
    Py_DECREF(py_cmsg);
    return nullptr;
  }

  return py_cmsg;
}

PyObject* DeepCopy(CMessage* self, PyObject* arg) {
  PyObject* clone =
      PyObject_CallObject(reinterpret_cast<PyObject*>(Py_TYPE(self)), nullptr);
  if (clone == nullptr) {
    return nullptr;
  }
  if (!PyObject_TypeCheck(clone, CMessage_Type)) {
    Py_DECREF(clone);
    return nullptr;
  }
  if (ScopedPyObjectPtr(MergeFrom(reinterpret_cast<CMessage*>(clone),
                                  reinterpret_cast<PyObject*>(self))) ==
      nullptr) {
    Py_DECREF(clone);
    return nullptr;
  }
  return clone;
}

PyObject* ToUnicode(CMessage* self) {
  // Lazy import to prevent circular dependencies
  ScopedPyObjectPtr text_format(
      PyImport_ImportModule(PROTOBUF_PYTHON_PUBLIC ".text_format"));
  if (text_format == nullptr) {
    return nullptr;
  }
  ScopedPyObjectPtr method_name(PyUnicode_FromString("MessageToString"));
  if (method_name == nullptr) {
    return nullptr;
  }
  Py_INCREF(Py_True);
  ScopedPyObjectPtr encoded(PyObject_CallMethodObjArgs(
      text_format.get(), method_name.get(), self, Py_True, nullptr));
  Py_DECREF(Py_True);
  if (encoded == nullptr) {
    return nullptr;
  }
  PyObject* decoded =
      PyUnicode_FromEncodedObject(encoded.get(), "utf-8", nullptr);
  if (decoded == nullptr) {
    return nullptr;
  }
  return decoded;
}

PyObject* Contains(CMessage* self, PyObject* arg) {
  Message* message = self->message;
  const Descriptor* descriptor = message->GetDescriptor();
  switch (descriptor->well_known_type()) {
    case Descriptor::WELLKNOWNTYPE_STRUCT: {
      // For WKT Struct, check if the key is in the fields.
      const Reflection* reflection = message->GetReflection();
      const FieldDescriptor* map_field = descriptor->FindFieldByName("fields");
      const FieldDescriptor* key_field = map_field->message_type()->map_key();
      MapKey map_key;
      std::optional<absl::string_view> key_string = CheckString(arg, key_field);
      if (!key_string.has_value()) {
        PyErr_Clear();
        PyErr_SetString(PyExc_TypeError,
                        "The key passed to Struct message must be a str.");
        return nullptr;
      }
      map_key.SetStringValue(*key_string);

      return PyBool_FromLong(MessageReflectionFriend::ContainsMapKey(
          reflection, *message, map_field, map_key));
    }
    case Descriptor::WELLKNOWNTYPE_LISTVALUE: {
      // For WKT ListValue, check if the key is in the items.
      ScopedPyObjectPtr items(PyObject_CallMethod(
          reinterpret_cast<PyObject*>(self), "items", nullptr));
      return PyBool_FromLong(PySequence_Contains(items.get(), arg));
    }
    default:
      // For other messages, check with HasField.
      return HasField(self, arg);
  }
}

// CMessage static methods:
PyObject* _CheckCalledFromGeneratedFile(PyObject* unused,
                                        PyObject* unused_arg) {
  if (!_CalledFromGeneratedFile(1)) {
    PyErr_SetString(PyExc_TypeError,
                    "Descriptors should not be created directly, "
                    "but only retrieved from their parent.");
    return nullptr;
  }
  Py_RETURN_NONE;
}

static PyObject* GetExtensionDict(CMessage* self, void* closure) {
  // If there are extension_ranges, the message is "extendable". Allocate a
  // dictionary to store the extension fields.
  const Descriptor* descriptor = GetMessageDescriptor(Py_TYPE(self));
  if (!descriptor->extension_range_count()) {
    PyErr_SetNone(PyExc_AttributeError);
    return nullptr;
  }
  ExtensionDict* extension_dict = extension_dict::NewExtensionDict(self);
  return reinterpret_cast<PyObject*>(extension_dict);
}

static PyObject* GetUnknownFields(CMessage* self) {
  PyErr_Format(PyExc_NotImplementedError,
               "Please use the add-on feature "
               "unknown_fields.UnknownFieldSet(message) in "
               "unknown_fields.py instead.");
  return nullptr;
}

static PyGetSetDef Getters[] = {
    {"Extensions", (getter)GetExtensionDict, nullptr, "Extension dict"},
    {nullptr},
};

static PyMethodDef Methods[] = {
    {"__deepcopy__", (PyCFunction)DeepCopy, METH_VARARGS,
     "Makes a deep copy of the class."},
    {"__unicode__", (PyCFunction)ToUnicode, METH_NOARGS,
     "Outputs a unicode representation of the message."},
    {"__contains__", (PyCFunction)Contains, METH_O,
     "Checks if a message field is set."},
    {"ByteSize", (PyCFunction)ByteSize, METH_NOARGS,
     "Returns the size of the message in bytes."},
    {"Clear", (PyCFunction)Clear, METH_NOARGS, "Clears the message."},
    {"ClearExtension", (PyCFunction)ClearExtension, METH_O,
     "Clears a message field."},
    {"ClearField", (PyCFunction)ClearField, METH_O, "Clears a message field."},
    {"CopyFrom", (PyCFunction)CopyFrom, METH_O,
     "Copies a protocol message into the current message."},
    {"DiscardUnknownFields", (PyCFunction)DiscardUnknownFields, METH_NOARGS,
     "Discards the unknown fields."},
    {"FindInitializationErrors", (PyCFunction)FindInitializationErrors,
     METH_NOARGS, "Finds unset required fields."},
    {"FromString", (PyCFunction)FromString, METH_O | METH_CLASS,
     "Creates new method instance from given serialized data."},
    {"HasExtension", (PyCFunction)HasExtension, METH_O,
     "Checks if a message field is set."},
    {"HasField", (PyCFunction)HasField, METH_O,
     "Checks if a message field is set."},
    {"IsInitialized", (PyCFunction)IsInitialized, METH_VARARGS,
     "Checks if all required fields of a protocol message are set."},
    {"ListFields", (PyCFunction)ListFields, METH_NOARGS,
     "Lists all set fields of a message."},
    {"MergeFrom", (PyCFunction)MergeFrom, METH_O,
     "Merges a protocol message into the current message."},
    {"MergeFromString", (PyCFunction)MergeFromString, METH_O,
     "Merges a serialized message into the current message."},
    {"ParseFromString", (PyCFunction)ParseFromString, METH_O,
     "Parses a serialized message into the current message."},
    {"SerializePartialToString", (PyCFunction)SerializePartialToString,
     METH_VARARGS | METH_KEYWORDS,
     "Serializes the message to a string, even if it isn't initialized."},
    {"SerializeToString", (PyCFunction)SerializeToString,
     METH_VARARGS | METH_KEYWORDS,
     "Serializes the message to a string, only for initialized messages."},
    {"SetInParent", (PyCFunction)SetInParent, METH_NOARGS,
     "Sets the has bit of the given field in its parent message."},
    {"UnknownFields", (PyCFunction)GetUnknownFields, METH_NOARGS,
     "Parse unknown field set"},
    {"WhichOneof", (PyCFunction)WhichOneof, METH_O,
     "Returns the name of the field set inside a oneof, "
     "or None if no field is set."},

    // Static Methods.
    {"_CheckCalledFromGeneratedFile",
     (PyCFunction)_CheckCalledFromGeneratedFile, METH_NOARGS | METH_STATIC,
     "Raises TypeError if the caller is not in a _pb2.py file."},
    {nullptr, nullptr}};

bool SetCompositeField(CMessage* self, const FieldDescriptor* field,
                       PyObject*& value) {
  self->composite_fields.Get()->TrySet(field, value);
  return true;
}

bool SetSubmessage(CMessage* self, CMessage*& submessage) {
  PyObject* obj = submessage->AsPyObject();
  self->child_submessages.Get()->TrySet(submessage->message, obj);
  submessage = reinterpret_cast<CMessage*>(obj);
  return true;
}

PyObject* GetAttr(PyObject* pself, PyObject* name) {
  CMessage* self = reinterpret_cast<CMessage*>(pself);
  PyObject* result =
      PyObject_GenericGetAttr(reinterpret_cast<PyObject*>(self), name);
  if (result != nullptr) {
    return result;
  }
  if (!PyErr_ExceptionMatches(PyExc_AttributeError)) {
    return nullptr;
  }

  PyErr_Clear();
  return message_meta::GetClassAttribute(CheckMessageClass(Py_TYPE(self)),
                                         name);
}

PyObject* GetFieldValue(CMessage* self,
                        const FieldDescriptor* field_descriptor) {
  if (CMessage::CompositeFieldsMap* fields = self->composite_fields.TryGet();
      fields != nullptr) {
    if (PyObject* value = fields->Get(field_descriptor, nullptr)) {
      return value;
    }
  }

  if (self->message->GetDescriptor() != field_descriptor->containing_type()) {
    PyErr_Format(PyExc_TypeError,
                 "descriptor to field '%s' doesn't apply to '%s' object",
                 std::string(field_descriptor->full_name()).c_str(),
                 Py_TYPE(self)->tp_name);
    return nullptr;
  }

  if (!field_descriptor->is_repeated() &&
      field_descriptor->cpp_type() != FieldDescriptor::CPPTYPE_MESSAGE) {
    return InternalGetScalar(self->message, field_descriptor);
  }

  ContainerBase* py_container = nullptr;
  if (field_descriptor->is_map()) {
    const Descriptor* entry_type = field_descriptor->message_type();
    const FieldDescriptor* value_type = entry_type->map_value();
    if (value_type->cpp_type() == FieldDescriptor::CPPTYPE_MESSAGE) {
      CMessageClass* value_class = message_factory::GetMessageClass(
          GetFactoryForMessage(self), value_type->message_type());
      if (value_class == nullptr) {
        return nullptr;
      }
      py_container =
          NewMessageMapContainer(self, field_descriptor, value_class);
    } else {
      py_container = NewScalarMapContainer(self, field_descriptor);
    }
  } else if (field_descriptor->is_repeated()) {
    if (field_descriptor->cpp_type() == FieldDescriptor::CPPTYPE_MESSAGE) {
      CMessageClass* message_class = message_factory::GetMessageClass(
          GetFactoryForMessage(self), field_descriptor->message_type());
      if (message_class == nullptr) {
        return nullptr;
      }
      py_container = repeated_composite_container::NewContainer(
          self, field_descriptor, message_class);
    } else {
      py_container =
          repeated_scalar_container::NewContainer(self, field_descriptor);
    }
  } else if (field_descriptor->cpp_type() == FieldDescriptor::CPPTYPE_MESSAGE) {
    py_container = InternalGetSubMessage(self, field_descriptor);
  } else {
    PyErr_SetString(PyExc_SystemError, "Should never happen");
  }

  if (py_container == nullptr) {
    return nullptr;
  }
  PyObject* value = py_container->AsPyObject();
  SetCompositeField(self, field_descriptor, value);
  return value;
}

int SetFieldValue(CMessage* self, const FieldDescriptor* field_descriptor,
                  PyObject* value) {
  if (self->message->GetDescriptor() != field_descriptor->containing_type()) {
    PyErr_Format(PyExc_TypeError,
                 "descriptor to field '%s' doesn't apply to '%s' object",
                 std::string(field_descriptor->full_name()).c_str(),
                 Py_TYPE(self)->tp_name);
    return -1;
  } else if (field_descriptor->is_repeated()) {
    PyErr_Format(PyExc_AttributeError,
                 "Assignment not allowed to repeated "
                 "field \"%s\" in protocol message object.",
                 std::string(field_descriptor->name()).c_str());
    return -1;
  } else if (field_descriptor->cpp_type() == FieldDescriptor::CPPTYPE_MESSAGE) {
    if (field_descriptor->message_type()->well_known_type() !=
        Descriptor::WELLKNOWNTYPE_UNSPECIFIED) {
      ScopedPyObjectPtr sub_message(GetFieldValue(self, field_descriptor));
      if (PyObject_HasAttrString(sub_message.get(), "_internal_assign")) {
        if (AssureWritable(self) < 0) return -1;
        ScopedPyObjectPtr ok(PyObject_CallMethod(
            sub_message.get(), "_internal_assign", "O", value));
        if (ok.get() == nullptr) {
          return -1;
        }
        return 0;
      }
    }
    PyErr_Format(PyExc_AttributeError,
                 "Assignment not allowed to "
                 "field \"%s\" in protocol message object.",
                 std::string(field_descriptor->name()).c_str());
    return -1;
  } else {
    if (AssureWritable(self) < 0) return -1;
    return InternalSetScalar(self, field_descriptor, value);
  }
}

}  // namespace cmessage

// All containers which are not messages:
// - Make a new parent message
// - Copy the field
// - return the field.
PyObject* ContainerBase::DeepCopy() {
  CMessage* new_parent =
      cmessage::NewEmptyMessage(this->parent->GetMessageClass());
  new_parent->message = this->parent->message->New(nullptr);

  // There is no API to copy a single field. The closest operation we have is
  // SwapFields.
  // So, we copy the source into a disposable message and then swap the one
  // field we care about from it.
  // If the performance of this operation matters we can do a copy of the single
  // field, but that would require huge switches for each type+cardinality to
  // call the right read/write field functions.
  std::unique_ptr<Message> tmp(this->parent->message->New(nullptr));
  tmp->MergeFrom(*this->parent->message);
  tmp->GetReflection()->SwapFields(tmp.get(), new_parent->message,
                                   {this->parent_field_descriptor});

  PyObject* result =
      cmessage::GetFieldValue(new_parent, this->parent_field_descriptor);
  Py_DECREF(new_parent);
  return result;
}

void ContainerBase::RemoveFromParentCache() {
  CMessage* parent = this->parent;
  if (parent) {
    if (CMessage::CompositeFieldsMap* fields =
            parent->composite_fields.TryGet()) {
      fields->Erase(this->parent_field_descriptor);
    }
    Py_CLEAR(parent);
  }
}

CMessage* CMessage::BuildSubMessageFromPointer(
    const FieldDescriptor* field_descriptor, Message* sub_message,
    CMessageClass* message_class) {
  if (PyObject* value =
          this->child_submessages.Get()->Get(sub_message, nullptr)) {
    return reinterpret_cast<CMessage*>(value);
  }

  CMessage* cmsg = cmessage::NewEmptyMessage(message_class);

  if (cmsg == nullptr) {
    return nullptr;
  }
  cmsg->message = sub_message;
  Py_INCREF(this);
  cmsg->parent = this;
  cmsg->parent_field_descriptor = field_descriptor;
  cmessage::SetSubmessage(this, cmsg);
  return cmsg;
}

CMessage* CMessage::MaybeReleaseSubMessage(Message* sub_message) {
  CMessage::SubMessagesMap* sub_messages = this->child_submessages.TryGet();
  if (sub_messages == nullptr) {
    return nullptr;
  }
  PyObject* value = sub_messages->Get(sub_message, nullptr);
  if (value == nullptr) return nullptr;
  CMessage* released = reinterpret_cast<CMessage*>(value);

  // The target message will now own its content.
  Py_CLEAR(released->parent);
  released->parent_field_descriptor = nullptr;
  released->read_only = false;
  // Delete it from the cache.
  sub_messages->Erase(sub_message);
  // child_submessages->Get returned a new reference.
  Py_DECREF(released);
  return released;
}

static CMessageClass _CMessage_Type = {{{
    PyVarObject_HEAD_INIT(&_CMessageClass_Type, 0) FULL_MODULE_NAME
    ".CMessage",                    // tp_name
    sizeof(CMessage),               // tp_basicsize
    0,                              //  tp_itemsize
    (destructor)cmessage::Dealloc,  //  tp_dealloc
#if PY_VERSION_HEX < 0x03080000
    nullptr,  // tp_print
#else
    0,  // tp_vectorcall_offset
#endif
    nullptr,                      //  tp_getattr
    nullptr,                      //  tp_setattr
    nullptr,                      //  tp_compare
    (reprfunc)cmessage::ToStr,    //  tp_repr
    nullptr,                      //  tp_as_number
    nullptr,                      //  tp_as_sequence
    nullptr,                      //  tp_as_mapping
    PyObject_HashNotImplemented,  //  tp_hash
    nullptr,                      //  tp_call
    (reprfunc)cmessage::ToStr,    //  tp_str
    cmessage::GetAttr,            //  tp_getattro
    nullptr,                      //  tp_setattro
    nullptr,                      //  tp_as_buffer
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE |
        Py_TPFLAGS_HAVE_VERSION_TAG,     //  tp_flags
    "A ProtocolMessage",                 //  tp_doc
    nullptr,                             //  tp_traverse
    nullptr,                             //  tp_clear
    (richcmpfunc)cmessage::RichCompare,  //  tp_richcompare
    offsetof(CMessage, weakreflist),     //  tp_weaklistoffset
    nullptr,                             //  tp_iter
    nullptr,                             //  tp_iternext
    cmessage::Methods,                   //  tp_methods
    nullptr,                             //  tp_members
    cmessage::Getters,                   //  tp_getset
    nullptr,                             //  tp_base
    nullptr,                             //  tp_dict
    nullptr,                             //  tp_descr_get
    nullptr,                             //  tp_descr_set
    0,                                   //  tp_dictoffset
    (initproc)cmessage::Init,            //  tp_init
    nullptr,                             //  tp_alloc
    cmessage::New,                       //  tp_new
}}};
PyTypeObject* CMessage_Type = &_CMessage_Type.super.ht_type;

// --- Exposing the C proto living inside Python proto to C code:

const Message* (*GetCProtoInsidePyProtoPtr)(PyObject* msg);
Message* (*MutableCProtoInsidePyProtoPtr)(PyObject* msg);

static const Message* GetCProtoInsidePyProtoImpl(PyObject* msg) {
  const Message* message = PyMessage_GetMessagePointer(msg);
  if (message == nullptr) {
    PyErr_Clear();
    return nullptr;
  }
  return message;
}

static Message* MutableCProtoInsidePyProtoImpl(PyObject* msg) {
  Message* message = PyMessage_GetMutableMessagePointer(msg);
  if (message == nullptr) {
    PyErr_Clear();
    return nullptr;
  }
  return message;
}

const Message* PyMessage_GetMessagePointer(PyObject* msg) {
  if (!PyObject_TypeCheck(msg, CMessage_Type)) {
    PyErr_SetString(PyExc_TypeError, "Not a Message instance");
    return nullptr;
  }
  CMessage* cmsg = reinterpret_cast<CMessage*>(msg);
  return cmsg->message;
}

Message* PyMessage_GetMutableMessagePointer(PyObject* msg) {
  if (!PyObject_TypeCheck(msg, CMessage_Type)) {
    PyErr_SetString(PyExc_TypeError, "Not a Message instance");
    return nullptr;
  }
  CMessage* cmsg = reinterpret_cast<CMessage*>(msg);
  CMessage::CompositeFieldsMap* fields = cmsg->composite_fields.TryGet();
  CMessage::SubMessagesMap* sub_messages = cmsg->child_submessages.TryGet();


  if ((fields != nullptr && !fields->IsEmpty()) ||
      (sub_messages != nullptr && !sub_messages->IsEmpty())) {
    // There is currently no way of accurately syncing arbitrary changes to
    // the underlying C++ message back to the CMessage (e.g. removed repeated
    // composite containers). We only allow direct mutation of the underlying
    // C++ message if there is no child data in the CMessage.
    PyErr_SetString(PyExc_ValueError,
                    "Cannot reliably get a mutable pointer "
                    "to a message with extra references");
    return nullptr;
  }
  if (cmessage::AssureWritable(cmsg) < 0) return nullptr;
  return cmsg->message;
}

// Returns a new reference to the MessageClass to use for message creation.
// - if a PyMessageFactory is passed, use it.
// - Otherwise, if a PyDescriptorPool was created, use its factory.
static CMessageClass* GetMessageClassFromDescriptor(
    const Descriptor* descriptor, PyObject* py_message_factory) {
  PyMessageFactory* factory = nullptr;
  if (py_message_factory == nullptr) {
    PyDescriptorPool* pool =
        GetDescriptorPool_FromPool(descriptor->file()->pool());
    if (pool == nullptr) {
      PyErr_SetString(PyExc_TypeError,
                      "Unknown descriptor pool; C++ users should call "
                      "DescriptorPool_FromPool and keep it alive");
      return nullptr;
    }
    factory = pool->py_message_factory;
  } else if (PyObject_TypeCheck(py_message_factory, &PyMessageFactory_Type)) {
    factory = reinterpret_cast<PyMessageFactory*>(py_message_factory);
  } else {
    PyErr_SetString(PyExc_TypeError, "Expected a MessageFactory");
    return nullptr;
  }

  return message_factory::GetOrCreateMessageClass(factory, descriptor);
}

PyObject* PyMessage_New(const Descriptor* descriptor,
                        PyObject* py_message_factory) {
  CMessageClass* message_class =
      GetMessageClassFromDescriptor(descriptor, py_message_factory);
  if (message_class == nullptr) {
    return nullptr;
  }

  CMessage* self = cmessage::NewCMessage(message_class);
  Py_DECREF(message_class);
  if (self == nullptr) {
    return nullptr;
  }
  return self->AsPyObject();
}

PyObject* PyMessage_NewMessageOwnedExternally(Message* message,
                                              PyObject* py_message_factory) {
  CMessageClass* message_class = GetMessageClassFromDescriptor(
      message->GetDescriptor(), py_message_factory);
  if (message_class == nullptr) {
    return nullptr;
  }

  CMessage* self = cmessage::NewEmptyMessage(message_class);
  Py_DECREF(message_class);
  if (self == nullptr) {
    return nullptr;
  }
  self->message = message;
  Py_INCREF(Py_None);
  self->parent = reinterpret_cast<CMessage*>(Py_None);
  return self->AsPyObject();
}

void InitGlobals() {
  // TODO: Check all return values in this function for NULL and propagate
  // the error (MemoryError) on up to result in an import failure.  These should
  // also be freed and reset to NULL during finalization.
  kDESCRIPTOR = PyUnicode_FromString("DESCRIPTOR");
  kMessageFactory = PyUnicode_FromString("message_factory");

  PyObject* dummy_obj = PySet_New(nullptr);
  kEmptyWeakref = PyWeakref_NewRef(dummy_obj, nullptr);
  Py_DECREF(dummy_obj);
}

bool InitProto2MessageModule(PyObject* m) {
  // Initialize types and globals in descriptor.cc
  if (!InitDescriptor()) {
    return false;
  }

  // Initialize types and globals in descriptor_pool.cc
  if (!InitDescriptorPool()) {
    return false;
  }

  // Initialize types and globals in message_factory.cc
  if (!InitMessageFactory()) {
    return false;
  }

  // Initialize constants defined in this file.
  InitGlobals();

  CMessageClass_Type->tp_base = &PyType_Type;
  if (PyType_Ready(CMessageClass_Type) < 0) {
    return false;
  }
  PyModule_AddObject(m, "MessageMeta",
                     reinterpret_cast<PyObject*>(CMessageClass_Type));

  if (PyType_Ready(CMessage_Type) < 0) {
    return false;
  }
  if (PyType_Ready(CFieldProperty_Type) < 0) {
    return false;
  }

  // DESCRIPTOR is set on each protocol buffer message class elsewhere, but set
  // it here as well to document that subclasses need to set it.
  PyDict_SetItem(CMessage_Type->tp_dict, kDESCRIPTOR, Py_None);
  // Invalidate any cached data for the CMessage type.
  // This call is necessary to correctly support Py_TPFLAGS_HAVE_VERSION_TAG,
  // after we have modified CMessage_Type.tp_dict.
  PyType_Modified(CMessage_Type);

  PyModule_AddObject(m, "Message", reinterpret_cast<PyObject*>(CMessage_Type));

  // Initialize Repeated container types.
  {
    if (PyType_Ready(&RepeatedScalarContainer_Type) < 0) {
      return false;
    }

    PyModule_AddObject(
        m, "RepeatedScalarContainer",
        reinterpret_cast<PyObject*>(&RepeatedScalarContainer_Type));

    if (PyType_Ready(&RepeatedCompositeContainer_Type) < 0) {
      return false;
    }

    PyModule_AddObject(
        m, "RepeatedCompositeContainer",
        reinterpret_cast<PyObject*>(&RepeatedCompositeContainer_Type));

    // Register them as MutableSequence.
    ScopedPyObjectPtr collections(PyImport_ImportModule("collections.abc"));
    if (collections == nullptr) {
      return false;
    }
    ScopedPyObjectPtr mutable_sequence(
        PyObject_GetAttrString(collections.get(), "MutableSequence"));
    if (mutable_sequence == nullptr) {
      return false;
    }
    if (ScopedPyObjectPtr(
            PyObject_CallMethod(mutable_sequence.get(), "register", "O",
                                &RepeatedScalarContainer_Type)) == nullptr) {
      return false;
    }
    if (ScopedPyObjectPtr(
            PyObject_CallMethod(mutable_sequence.get(), "register", "O",
                                &RepeatedCompositeContainer_Type)) == nullptr) {
      return false;
    }
  }

  if (PyType_Ready(&PyUnknownFieldSet_Type) < 0) {
    return false;
  }

  PyModule_AddObject(m, "UnknownFieldSet",
                     reinterpret_cast<PyObject*>(&PyUnknownFieldSet_Type));

  if (PyType_Ready(&PyUnknownField_Type) < 0) {
    return false;
  }

  // Initialize Map container types.
  if (!InitMapContainers()) {
    return false;
  }
  PyModule_AddObject(m, "ScalarMapContainer",
                     reinterpret_cast<PyObject*>(ScalarMapContainer_Type));
  PyModule_AddObject(m, "MessageMapContainer",
                     reinterpret_cast<PyObject*>(MessageMapContainer_Type));
  PyModule_AddObject(m, "MapIterator",
                     reinterpret_cast<PyObject*>(&MapIterator_Type));

  if (PyType_Ready(&ExtensionDict_Type) < 0) {
    return false;
  }
  PyModule_AddObject(m, "ExtensionDict",
                     reinterpret_cast<PyObject*>(&ExtensionDict_Type));
  if (PyType_Ready(&ExtensionIterator_Type) < 0) {
    return false;
  }
  PyModule_AddObject(m, "ExtensionIterator",
                     reinterpret_cast<PyObject*>(&ExtensionIterator_Type));

  // Expose the DescriptorPool used to hold all descriptors added from generated
  // pb2.py files.
  // PyModule_AddObject steals a reference.
  Py_INCREF(GetDefaultDescriptorPool());
  PyModule_AddObject(m, "default_pool",
                     reinterpret_cast<PyObject*>(GetDefaultDescriptorPool()));

  PyModule_AddObject(m, "DescriptorPool",
                     reinterpret_cast<PyObject*>(&PyDescriptorPool_Type));
  PyModule_AddObject(m, "Descriptor",
                     reinterpret_cast<PyObject*>(&PyMessageDescriptor_Type));
  PyModule_AddObject(m, "FieldDescriptor",
                     reinterpret_cast<PyObject*>(&PyFieldDescriptor_Type));
  PyModule_AddObject(m, "EnumDescriptor",
                     reinterpret_cast<PyObject*>(&PyEnumDescriptor_Type));
  PyModule_AddObject(m, "EnumValueDescriptor",
                     reinterpret_cast<PyObject*>(&PyEnumValueDescriptor_Type));
  PyModule_AddObject(m, "FileDescriptor",
                     reinterpret_cast<PyObject*>(&PyFileDescriptor_Type));
  PyModule_AddObject(m, "OneofDescriptor",
                     reinterpret_cast<PyObject*>(&PyOneofDescriptor_Type));
  PyModule_AddObject(m, "ServiceDescriptor",
                     reinterpret_cast<PyObject*>(&PyServiceDescriptor_Type));
  PyModule_AddObject(m, "MethodDescriptor",
                     reinterpret_cast<PyObject*>(&PyMethodDescriptor_Type));

  PyObject* enum_type_wrapper =
      PyImport_ImportModule(PROTOBUF_PYTHON_INTERNAL ".enum_type_wrapper");
  if (enum_type_wrapper == nullptr) {
    return false;
  }
  EnumTypeWrapper_class =
      PyObject_GetAttrString(enum_type_wrapper, "EnumTypeWrapper");
  Py_DECREF(enum_type_wrapper);

  PyObject* message_module =
      PyImport_ImportModule(PROTOBUF_PYTHON_PUBLIC ".message");
  if (message_module == nullptr) {
    return false;
  }
  EncodeError_class = PyObject_GetAttrString(message_module, "EncodeError");
  DecodeError_class = PyObject_GetAttrString(message_module, "DecodeError");
  PythonMessage_class = PyObject_GetAttrString(message_module, "Message");
  Py_DECREF(message_module);

  PyObject* pickle_module = PyImport_ImportModule("pickle");
  if (pickle_module == nullptr) {
    return false;
  }
  PickleError_class = PyObject_GetAttrString(pickle_module, "PickleError");
  Py_DECREF(pickle_module);

  // Override {Get,Mutable}CProtoInsidePyProto.
  GetCProtoInsidePyProtoPtr = GetCProtoInsidePyProtoImpl;
  MutableCProtoInsidePyProtoPtr = MutableCProtoInsidePyProtoImpl;

  return true;
}

}  // namespace python
}  // namespace protobuf
}  // namespace google

#include "google/protobuf/port_undef.inc"
