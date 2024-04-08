#include <lean/lean.h>
#include <stdio.h>

typedef enum rw_dirs {
  NONE,
  FORWARD,
  BACKWARD,
  BOTH
} rw_dirs;

typedef struct rewrite {
    const char* name;
    const char* lhs;
    const char* rhs;
    rw_dirs dirs;
} rewrite;

/*
structure Rewrite.Encoded where
  name : String
  lhs  : Expression
  rhs  : Expression
  dirs : Rewrite.Directions

abbrev Expression := String

inductive Rewrite.Directions where
  | none
  | forward
  | backward
  | both
*/
rewrite rewrite_from_lean_obj(lean_obj_arg rw) {
    unsigned scalar_base_offset = lean_ctor_num_objs(rw) * sizeof(void*);
    return (rewrite) {
        .name = lean_string_cstr(lean_ctor_get(rw, 0)),
        .lhs  = lean_string_cstr(lean_ctor_get(rw, 1)),
        .rhs  = lean_string_cstr(lean_ctor_get(rw, 2)),
        .dirs = lean_ctor_get_uint8(rw, scalar_base_offset + 0),
    };
}

rewrite* rewrites_from_lean_obj(lean_obj_arg rws) {
    lean_object** rws_c_ptr = lean_array_cptr(rws);
    size_t rws_count = lean_array_size(rws);
    rewrite* rust_rws = malloc(rws_count * sizeof(rewrite));
    for (int idx = 0; idx < rws_count; idx++) {
        rust_rws[idx] = rewrite_from_lean_obj(rws_c_ptr[idx]);
    }
    return rust_rws;
}

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

// TODO: Remove this.
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

// `init`: string
// `goal`: string
// `rws`: array of `Egg.Rewrite.Encoded`
// `viz_path`: string
// `cfg`: an `Egg.Request.Config`
// return value: string explaining the rewrite sequence
lean_obj_res lean_egg_explain_congr(lean_obj_arg init, lean_obj_arg goal, lean_obj_arg rws, lean_obj_arg viz_path, lean_obj_arg cfg) {
    const char* init_c_str = lean_string_cstr(init);
    const char* goal_c_str = lean_string_cstr(goal);
    rewrite* rust_rws = rewrites_from_lean_obj(rws);
    size_t rws_count = lean_array_size(rws);
    const char* viz_path_c_str = lean_string_cstr(viz_path);
    config rust_cfg = config_from_lean_obj(cfg);

    egg_result result = c_egg_explain_congr(init_c_str, goal_c_str, rust_rws, rws_count, rust_cfg, viz_path_c_str);
    free(rust_rws);

    return lean_mk_string(result.expl);
}

lean_object* dbg_trace_thunk(lean_object* t) { return lean_box(0); }
void c_dbg_trace(char const* str) {
    lean_object* thunk_obj = lean_alloc_closure(&dbg_trace_thunk, 1, 0);
    lean_object* lstr = lean_mk_string(str);
    lean_dbg_trace(lstr, thunk_obj);
    return;
}