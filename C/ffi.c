#include <lean/lean.h>
#include <stdio.h>

typedef enum rw_dir {
  FORWARD,
  BACKWARD,
  BOTH
} rw_dir;

typedef struct rewrite {
    char* name;
    char* lhs;
    char* rhs;
    rw_dir dir;
} rewrite;

typedef struct egg_result {
    _Bool success;
    char* expl;
} egg_result;

extern egg_result c_egg_check_eq(const char* init, const char* goal, rewrite* rws, size_t rws_count);

// TODO: Remove
lean_object* thunk(lean_object* t) { return lean_box(0); }
void trace(char const* str) {
    lean_object* thunk_obj = lean_alloc_closure(&thunk, 1, 0);
    lean_object* lstr = lean_mk_string(str);
    lean_dbg_trace(lstr, thunk_obj);
    return;
}

// `init`: string
// `goal`: string
// `rw_names`: array of strings containing the names of rewrites
// `rw_lhss`: array of strings containing the left-hands sides of rewrites
// `rw_rhss`: array of strings containing the right-hands sides of rewrites
// `rw_dirs`: array of uint8_t containing the directions (cf. `rw_dir`) of rewrites
// return value: string explaining the rewrite sequence
lean_obj_res lean_egg_check_eq(lean_obj_arg init, lean_obj_arg goal, lean_obj_arg rw_names, lean_obj_arg rw_lhss, lean_obj_arg rw_rhss, lean_obj_arg rw_dirs) {
    const char* init_c_str = lean_string_cstr(init);
    const char* goal_c_str = lean_string_cstr(goal);
    lean_object** rw_names_c_ptr = lean_array_cptr(rw_names);
    lean_object** rw_lhss_c_ptr = lean_array_cptr(rw_lhss);
    lean_object** rw_rhss_c_ptr = lean_array_cptr(rw_rhss);
    lean_object** rw_dirs_c_ptr = lean_array_cptr(rw_dirs);
    size_t rws_count = lean_array_size(rw_names);
    assert(rws_count == lean_array_size(rw_lhss));
    assert(rws_count == lean_array_size(rw_rhss));
    assert(rws_count == lean_array_size(rw_dirs));
    rewrite* rws = malloc(rws_count * sizeof(rewrite));
    for (int idx = 0; idx < rws_count; idx++) {
        const char* name = lean_string_cstr(rw_names_c_ptr[idx]);
        const char* lhs  = lean_string_cstr(rw_lhss_c_ptr[idx]);
        const char* rhs  = lean_string_cstr(rw_rhss_c_ptr[idx]);
        rw_dir dir       = lean_unbox(rw_dirs_c_ptr[idx]);
        rws[idx] = (rewrite) { .name = name, .lhs = lhs, .rhs = rhs, .dir = dir };
    }

    egg_result result = c_egg_check_eq(init_c_str, goal_c_str, rws, rws_count);
    free(rws);

    if (result.success) {
        return lean_mk_string(result.expl);
    } else {
        char empty[1] = "";
        return lean_mk_string(empty);
    }
    /*
    trace(init_c_str);
    trace(goal_c_str);
    for (int idx = 0; idx < rws_count; idx++) {
        trace(rws[idx].name);
        trace(rws[idx].lhs);
        trace(rws[idx].rhs);

        char* d;
        if (rws[idx].dir == FORWARD) { d = "fw"; }
        else if (rws[idx].dir == BACKWARD) { d = "ba"; }
        else if (rws[idx].dir == BOTH) { d = "bo"; }
        else { d = "NA"; }
        trace(d);
    }
    char* e = are_eq ? "iseq" : "noteq" ;
    trace(e);
    char* c = rws_count == 1 ? "1" : "!=1";
    trace(c);
    */
}