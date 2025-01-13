#include <lean/lean.h>
#include <stdlib.h>
#include "ffi.h"

// Returns `EStateM.Result Exception PUnit Bool`.
extern lean_obj_res lean_is_synthable(
    lean_object* ty_str,
    lean_object* x1,
    lean_object* x2,
    lean_object* x3,
    lean_object* x4,
    lean_object* x5
);

_Bool is_synthable(const void* v, const char* str) {
    env* e = (env*)v;
    lean_obj_res ty_str = lean_mk_string(str);
    
    lean_inc(e->x1); lean_inc(e->x2); lean_inc(e->x3); lean_inc(e->x4); lean_inc(e->x5);
    lean_obj_res s = lean_is_synthable(ty_str, e->x1, e->x2, e->x3, e->x4, e->x5);
    
    switch (s->m_tag) {
        /* EStateM.Result.ok */ case 0: {
            // Note: The `Bool` is boxed for some reason.
            lean_obj_res b = lean_ctor_get(s, 0);
            size_t result = lean_unbox(b);
            return result != 0;
        }
        /* EStateM.Result.err */ case 1: {
            return false;
            // TODO: We should propagate the error back, as it would also be important
            //       to know whether we have a `MetaM` failure when we return from `runRaw`.
        }
        default: {
            exit(1);
        }
    }
}