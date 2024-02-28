#include <lean/lean.h>
#include <stdio.h>

typedef uint8_t lean_bool;
typedef _Bool rust_bool;

rust_bool lean_bool_to_rust(lean_bool b) {
    return b;
}

typedef enum rw_dir {
  NONE,
  FORWARD,
  BACKWARD,
  BOTH
} rw_dir;

typedef struct rewrite {
    const char* name;
    const char* lhs;
    const char* rhs;
    rw_dir dir;
} rewrite;

typedef struct egg_result {
    rust_bool success;
    char* expl;
} egg_result;

extern egg_result c_egg_explain_congr(
    const char* init, 
    const char* goal, 
    rewrite* rws, 
    size_t rws_count, 
    rust_bool optimize_expl,
    rust_bool gen_nat_lit_rws,
    const char* viz_path
);

// `init`: string
// `goal`: string
// `rw_names`: array of strings containing the names of rewrites
// `rw_lhss`: array of strings containing the left-hands sides of rewrites
// `rw_rhss`: array of strings containing the right-hands sides of rewrites
// `rw_dirs`: array of uint8_t containing the directions (cf. `rw_dir`) of rewrites
// `optimize_expl`: boolean indicating whether egg should try to shorten its explanations
// `gen_nat_lit_rws`: boolean indicating whether egg should use additional rewrites to convert between nat-lits and `Nat.zero`/`Nat.succ`
// `viz_path`: string
// return value: string explaining the rewrite sequence
lean_obj_res lean_egg_explain_congr(
    lean_obj_arg init, 
    lean_obj_arg goal, 
    lean_obj_arg rw_names, 
    lean_obj_arg rw_lhss, 
    lean_obj_arg rw_rhss, 
    lean_obj_arg rw_dirs,
    lean_bool optimize_expl,
    lean_bool gen_nat_lit_rws,
    lean_obj_arg viz_path
) {
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
        rw_dir dir = lean_unbox(rw_dirs_c_ptr[idx]);
        rws[idx] = (rewrite) { .name = name, .lhs = lhs, .rhs = rhs, .dir = dir };
    }
    rust_bool opt_expl = lean_bool_to_rust(optimize_expl);
    rust_bool nat_lit_rws = lean_bool_to_rust(gen_nat_lit_rws);
    const char* viz_path_c_str = lean_string_cstr(viz_path);

    egg_result result = c_egg_explain_congr(init_c_str, goal_c_str, rws, rws_count, opt_expl, nat_lit_rws, viz_path_c_str);
    free(rws);

    return lean_mk_string(result.expl);
}