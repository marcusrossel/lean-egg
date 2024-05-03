#include <lean/lean.h>
#include <stdio.h>

size_t nat_from_lean_obj(lean_obj_arg nat) {
    assert(lean_is_scalar(nat));
    return lean_unbox(nat);
}

typedef struct str_array {
    const char** ptr;
    size_t       len;
} str_array;

str_array str_array_from_lean_obj(lean_obj_arg strs) {
    lean_object** strs_c_ptr = lean_array_cptr(strs);
    size_t strs_count = lean_array_size(strs);
    const char** c_strs = malloc(strs_count * sizeof(const char*));
    for (int idx = 0; idx < strs_count; idx++) {
        c_strs[idx] = lean_string_cstr(strs_c_ptr[idx]);
    }
    return (str_array) { .ptr = c_strs, .len = strs_count };
}

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
    rw_dirs     dirs;
    str_array   conds;
} rewrite;

/*
structure Rewrite.Encoded where
  name  : String
  lhs   : String
  rhs   : String
  dirs  : Directions
  conds : Array String

inductive Directions where
  | none
  | forward
  | backward
  | both
*/
rewrite rewrite_from_lean_obj(lean_obj_arg rw) {
    unsigned scalar_base_offset = lean_ctor_num_objs(rw) * sizeof(void*);
    return (rewrite) {
        .name  = lean_string_cstr(lean_ctor_get(rw, 0)),
        .lhs   = lean_string_cstr(lean_ctor_get(rw, 1)),
        .rhs   = lean_string_cstr(lean_ctor_get(rw, 2)),
        .dirs  = lean_ctor_get_uint8(rw, scalar_base_offset + 0),
        .conds = str_array_from_lean_obj(lean_ctor_get(rw, 3))
    };
}

typedef struct rws_array {
    rewrite* ptr;
    size_t   len;
} rws_array;

rws_array rewrites_from_lean_obj(lean_obj_arg rws) {
    lean_object** rws_c_ptr = lean_array_cptr(rws);
    size_t rws_count = lean_array_size(rws);
    rewrite* rust_rws = malloc(rws_count * sizeof(rewrite));
    for (int idx = 0; idx < rws_count; idx++) {
        rust_rws[idx] = rewrite_from_lean_obj(rws_c_ptr[idx]);
    }
    return (rws_array) { .ptr = rust_rws, .len = rws_count };
}

void free_rws_array(rws_array rws) {
    for (int idx = 0; idx < rws.len; idx++) {
        free(rws.ptr[idx].conds.ptr);
    }
    free(rws.ptr);
}

/*
structure Fact.Encoded where
  name : String
  expr : String
*/
typedef struct fact {
    const char* name;
    const char* expr;
} fact;

fact fact_from_lean_obj(lean_obj_arg f) {
    return (fact) {
        .name = lean_string_cstr(lean_ctor_get(f, 0)),
        .expr = lean_string_cstr(lean_ctor_get(f, 1))
    };
}

typedef struct facts_array {
    fact*  ptr;
    size_t len;
} facts_array;

facts_array facts_from_lean_obj(lean_obj_arg facts) {
    lean_object** facts_c_ptr = lean_array_cptr(facts);
    size_t facts_count = lean_array_size(facts);
    fact* rust_facts = malloc(facts_count * sizeof(fact));
    for (int idx = 0; idx < facts_count; idx++) {
        rust_facts[idx] = fact_from_lean_obj(facts_c_ptr[idx]);
    }
    return (facts_array) { .ptr = rust_facts, .len = facts_count };
}

typedef struct config {
    _Bool  optimize_expl;
    size_t time_limit;
    _Bool  gen_nat_lit_rws;
    _Bool  gen_eta_rw;
    _Bool  gen_beta_rw;
    _Bool  block_invalid_matches;
    _Bool  shift_captured_bvars;
    _Bool  trace_substitutions;
    _Bool  trace_bvar_correction;
} config;

/*
structure Config where
  optimizeExpl        : Bool
  timeLimit           : Nat
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
        .time_limit            = nat_from_lean_obj(lean_ctor_get(cfg, 0)),  
        .gen_nat_lit_rws       = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 1),  
        .gen_eta_rw            = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 2),  
        .gen_beta_rw           = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 3),  
        .block_invalid_matches = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 4),  
        .shift_captured_bvars  = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 5),  
        .trace_substitutions   = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 6),  
        .trace_bvar_correction = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 7),  
    };
}

typedef void* egraph;

extern void free_egraph(egraph);

void egraph_finalize(egraph obj) {
    free_egraph(obj);
}

void egraph_foreach(egraph _x, b_lean_obj_arg _y) {
    // do nothing since `egraph` does not contain nested Lean objects
}

static lean_external_class* egraph_class = NULL;

lean_object* egraph_to_lean(egraph e) {
    if (egraph_class == NULL) {
        egraph_class = lean_register_external_class(egraph_finalize, egraph_foreach);
    }
    return lean_alloc_external(egraph_class, e);
}

egraph to_egraph(b_lean_obj_arg e) {
    return (egraph)(lean_get_external_data(e));
}

typedef struct egg_result {
    char* expl;
    egraph graph;
} egg_result;

extern egg_result egg_explain_congr(
    const char* init, 
    const char* goal, 
    rws_array rws, 
    facts_array facts, 
    str_array guides, 
    config cfg,
    const char* viz_path
);

/*
structure Egg.Request where
  lhs     : String
  rhs     : String
  rws     : Array Rewrite.Encoded
  facts   : Array Fact.Encoded
  guides  : Array String
  vizPath : String
  cfg     : Request.Config
*/
egg_result run_egg_request_core(lean_obj_arg req) {
    const char* lhs      = lean_string_cstr(lean_ctor_get(req, 0));
    const char* rhs      = lean_string_cstr(lean_ctor_get(req, 1));
    rws_array rws        = rewrites_from_lean_obj(lean_ctor_get(req, 2));
    facts_array facts    = facts_from_lean_obj(lean_ctor_get(req, 3));
    str_array guides     = str_array_from_lean_obj(lean_ctor_get(req, 4));
    const char* viz_path = lean_string_cstr(lean_ctor_get(req, 5));
    config cfg           = config_from_lean_obj(lean_ctor_get(req, 6));

    egg_result result = egg_explain_congr(lhs, rhs, rws, facts, guides, cfg, viz_path);
    
    // TODO: Is it safe to free this?
    free_rws_array(rws);
    free(facts.ptr);
    free(guides.ptr);
    
    return result;
}

lean_obj_res run_egg_request(lean_obj_arg req) {
    egg_result result = run_egg_request_core(req);
    lean_object* expl = lean_mk_string(result.expl);
    lean_object* graph = egraph_to_lean(result.graph);
    
    lean_object* graph_opt;
    if (graph == NULL) {
        graph_opt = lean_alloc_ctor(0, 0, 0); // Option.nil
    } else {
        graph_opt = lean_alloc_ctor(1, 1, 0); // Option.some
        lean_ctor_set(graph_opt, 0, graph);
    }

    lean_object* pair = lean_alloc_ctor(0, 2, 0); // Prod.mk
    lean_ctor_set(pair, 0, expl);
    lean_ctor_set(pair, 1, graph_opt);

    return pair;
}

extern const char* egg_query_equiv(
    egraph graph,
    const char* init, 
    const char* goal
);

lean_obj_res explain_equiv(b_lean_obj_arg graph, lean_obj_arg init, lean_obj_arg goal) {
    egraph graph_c     = to_egraph(graph);
    const char* init_c = lean_string_cstr(init);
    const char* goal_c = lean_string_cstr(goal);
    return lean_mk_string(egg_query_equiv(graph_c, init_c, goal_c));
}

/*
lean_object* dbg_trace_thunk(lean_object* t) { return lean_box(0); }
void c_dbg_trace(char const* str) {
    lean_object* thunk_obj = lean_alloc_closure(&dbg_trace_thunk, 1, 0);
    lean_object* lstr = lean_mk_string(str);
    lean_dbg_trace(lstr, thunk_obj);
    return;
}
*/