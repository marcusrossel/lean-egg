#include <lean/lean.h>
#include "ffi.h"

extern lean_obj_res lean_is_synthable(
    lean_obj_arg ty_str,
    lean_obj_arg x1,
    lean_obj_arg x2,
    lean_obj_arg x3,
    lean_obj_arg x4,
    lean_obj_arg x5
);

_Bool is_synthable(const void* v, const char* str) {
    env* e = (env*)v;
    lean_obj_res ty_str = lean_mk_string(str);
    lean_obj_res s = lean_is_synthable(ty_str, e->x1, e->x2, e->x3, e->x4, e->x5);
    // The layout of `s` consists of one object and one boolean.
    // TODO: Is `IO.RealWorld` a scalar?
    size_t scalar_base_offset = 1 * sizeof(void*);
    uint8_t result = lean_ctor_get_uint8(s, scalar_base_offset + 0);
    return result != 0;
}
