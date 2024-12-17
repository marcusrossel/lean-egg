#include <lean/lean.h>
#include "ffi.h"

extern lean_object* is_synthable(
    lean_obj_arg ty_str,
    lean_obj_arg x1,
    lean_obj_arg x2,
    lean_obj_arg x3,
    lean_obj_arg x4,
    lean_obj_arg x5,
);

int handle_type_class_inst(env* e, const char* x) {
    lean_object* o = is_synthable(x, e.x_1, e.x_2, e.x_3, e.x_4, e.x_5);
    // lean_object* state = lean_ctor_get(o, 0);
    uint8_t b = lean_ctor_get_uint8(o, sizeof(void*));
    return b;
}
