#include <lean/lean.h>
#include <stdio.h>

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

typedef struct config {
    _Bool optimize_expl;
    _Bool gen_nat_lit_rws;
    _Bool gen_eta_rw;
    _Bool gen_beta_rw;
    _Bool block_invalid_matches;
    _Bool shift_captured_bvars;
    _Bool trace_substitutions;
    _Bool trace_bvar_correction;
} config;

typedef struct egg_result {
    _Bool success;
    char* expl;
} egg_result;

extern egg_result c_egg_explain_congr(
    const char* init, 
    const char* goal, 
    rewrite* rws, 
    size_t rws_count, 
    config cfg,
    const char* viz_path
);

/*
structure Config where
  optimizeExpl        : Bool
  genNatLitRws        : Bool
  genEtaRw            : Bool
  genBetaRw           : Bool
  blockInvalidMatches : Bool
  shiftCapturedBVars  : Bool
  traceSubstitutions  : Bool
  traceBVarCorrection : Bool
*/
config config_from_lean_obj(lean_obj_arg cfg) {
    unsigned scalar_base_offset = lean_ctor_num_objs(cfg) * sizeof(void*);
    unsigned bool_offset = sizeof(uint8_t);
    return (config) { 
        .optimize_expl         = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 0),  
        .gen_nat_lit_rws       = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 1),  
        .gen_eta_rw            = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 2),  
        .gen_beta_rw           = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 3),  
        .block_invalid_matches = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 4),  
        .shift_captured_bvars  = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 5),  
        .trace_substitutions   = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 6),  
        .trace_bvar_correction = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 7),  
    };
}

// `init`: string
// `goal`: string
// `rw_names`: array of strings containing the names of rewrites
// `rw_lhss`: array of strings containing the left-hands sides of rewrites
// `rw_rhss`: array of strings containing the right-hands sides of rewrites
// `rw_dirs`: array of uint8_t containing the directions (cf. `rw_dir`) of rewrites
// `viz_path`: string
// `cfg`: an `Egg.Request.Config`
// return value: string explaining the rewrite sequence
lean_obj_res lean_egg_explain_congr(
    lean_obj_arg init, 
    lean_obj_arg goal, 
    lean_obj_arg rw_names, 
    lean_obj_arg rw_lhss, 
    lean_obj_arg rw_rhss, 
    lean_obj_arg rw_dirs,
    lean_obj_arg viz_path,
    lean_obj_arg cfg
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
    const char* viz_path_c_str = lean_string_cstr(viz_path);
    config rust_cfg = config_from_lean_obj(cfg);

    egg_result result = c_egg_explain_congr(init_c_str, goal_c_str, rws, rws_count, rust_cfg, viz_path_c_str);
    free(rws);

    return lean_mk_string(result.expl);
}

lean_object* dbg_trace_thunk(lean_object* t) { return lean_box(0); }
void c_dbg_trace(char const* str) {
    lean_object* thunk_obj = lean_alloc_closure(&dbg_trace_thunk, 1, 0);
    lean_object* lstr = lean_mk_string(str);
    lean_dbg_trace(lstr, thunk_obj);
    return;
}