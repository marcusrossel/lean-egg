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
    size_t node_limit;
    size_t iter_limit;
    _Bool  nat_lit;
    _Bool  eta;
    _Bool  eta_expand;
    _Bool  beta;
    _Bool  levels;
    _Bool  shapes;
    _Bool  block_invalid_matches;
    _Bool  shift_captured_bvars;
    _Bool  union_semantics;
    _Bool  allow_unsat_conditions;
} config;

typedef struct lean_config {
    _Bool  slotted;
    config rust_config;
} lean_config;

/*
structure Config where
  slotted              : Bool
  optimizeExpl         : Bool
  timeLimit            : Nat
  nodeLimit            : Nat
  iterLimit            : Nat
  natLit               : Bool
  eta                  : Bool
  etaExpand            : Bool
  beta                 : Bool
  levels               : Bool
  shapes               : Bool
  blockInvalidMatches  : Bool
  shiftCapturedBVars   : Bool
  unionSemantics       : Bool
  allowUnsatConditions : Bool
*/
lean_config config_from_lean_obj(lean_obj_arg cfg) {
    unsigned scalar_base_offset = lean_ctor_num_objs(cfg) * sizeof(void*);
    unsigned bool_offset = sizeof(uint8_t);
    return (lean_config) { 
        .slotted = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 0),
        .rust_config = (config) {
            .optimize_expl          = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 1),
            .time_limit             = nat_from_lean_obj(lean_ctor_get(cfg, 0)),
            .node_limit             = nat_from_lean_obj(lean_ctor_get(cfg, 1)),
            .iter_limit             = nat_from_lean_obj(lean_ctor_get(cfg, 2)),  
            .nat_lit                = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 2),  
            .eta                    = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 3),  
            .eta_expand             = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 4),  
            .beta                   = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 5),  
            .levels                 = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 6),  
            .shapes                 = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 7), 
            .block_invalid_matches  = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 8), 
            .shift_captured_bvars   = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 9),  
            .union_semantics        = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 10),
            .allow_unsat_conditions = lean_ctor_get_uint8(cfg, scalar_base_offset + bool_offset * 11),  
        }
    };
}

/*
inductive StopReason where
  | saturated
  | timeLimit
  | iterationLimit
  | nodeLimit
  | other
*/

typedef enum stop_reason {
    SATURATED,
    TIME_LIMIT,
    ITERATION_LIMIT,
    NODE_LIMIT,
    OTHER
} stop_reason;

uint8_t stop_reason_to_lean(stop_reason reason) {
    return (uint8_t)reason;
}

/*
structure Report where
  iterations:  Nat
  stopReason:  StopReason
  nodeCount:   Nat
  classCount:  Nat
  time:        Float
  rwStats:     String
*/

typedef struct report {
    size_t      iterations;
    stop_reason reason;
    size_t      node_count;
    size_t      class_count;
    double      time;
    char*       rw_stats;
} report;

lean_obj_res report_to_lean(report rep) {
    lean_object* r = lean_alloc_ctor(0, 4, sizeof(double) + sizeof(uint8_t));
    size_t obj_offset = 4 * sizeof(void*);

    lean_ctor_set(r, 0, lean_box(rep.iterations));
    lean_ctor_set(r, 1, lean_box(rep.node_count));
    lean_ctor_set(r, 2, lean_box(rep.class_count));
    lean_ctor_set(r, 3, lean_mk_string(rep.rw_stats));
    lean_ctor_set_float(r, obj_offset, rep.time);
    lean_ctor_set_uint8(r, obj_offset + sizeof(double), stop_reason_to_lean(rep.reason));

    return r;
}

typedef void* egg_egraph;
typedef void* slotted_egraph;

extern void egg_free_egraph(egg_egraph);
extern void slotted_free_egraph(slotted_egraph);

void egg_egraph_finalize(egg_egraph obj) {
    egg_free_egraph(obj);
}

void slotted_egraph_finalize(slotted_egraph obj) {
    slotted_free_egraph(obj);
}

void egg_egraph_foreach(egg_egraph _x, b_lean_obj_arg _y) {
    // do nothing since `egg_egraph` does not contain nested Lean objects
}

void slotted_egraph_foreach(slotted_egraph _x, b_lean_obj_arg _y) {
    // do nothing since `slotted_egraph` does not contain nested Lean objects
}

static lean_external_class* egg_egraph_class = NULL;
static lean_external_class* slotted_egraph_class = NULL;

lean_object* egg_egraph_to_lean(egg_egraph e) {
    if (egg_egraph_class == NULL) {
        egg_egraph_class = lean_register_external_class(egg_egraph_finalize, egg_egraph_foreach);
    }
    return lean_alloc_external(egg_egraph_class, e);
}

lean_object* slotted_egraph_to_lean(slotted_egraph e) {
    if (slotted_egraph_class == NULL) {
        slotted_egraph_class = lean_register_external_class(slotted_egraph_finalize, slotted_egraph_foreach);
    }
    return lean_alloc_external(slotted_egraph_class, e);
}

egg_egraph to_egg_egraph(b_lean_obj_arg e) {
    return (egg_egraph)(lean_get_external_data(e));
}

slotted_egraph to_slotted_egraph(b_lean_obj_arg e) {
    return (slotted_egraph)(lean_get_external_data(e));
}

typedef struct egg_result {
    char* expl;
    egg_egraph graph;
    report rep;
} egg_result;

typedef struct slotted_result {
    char* expl;
    slotted_egraph graph;
    report rep;
} slotted_result;

typedef union egraph {
    egg_egraph egg;
    slotted_egraph slotted;
} egraph;

lean_object* egraph_to_lean(egraph e, _Bool slotted) {
    if (slotted) {
        return slotted_egraph_to_lean(e.slotted);
    } else {
        return egg_egraph_to_lean(e.egg);
    }
}

typedef struct eqsat_result {
    _Bool slotted;
    char* expl;
    egraph graph;
    report rep;
} eqsat_result;

extern egg_result egg_explain_congr(
    const char* init, 
    const char* goal, 
    rws_array rws, 
    facts_array facts, 
    str_array guides, 
    config cfg,
    const char* viz_path
);

extern slotted_result slotted_explain_congr(
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
eqsat_result run_eqsat_request_core(lean_obj_arg req) {
    const char* lhs      = lean_string_cstr(lean_ctor_get(req, 0));
    const char* rhs      = lean_string_cstr(lean_ctor_get(req, 1));
    rws_array rws        = rewrites_from_lean_obj(lean_ctor_get(req, 2));
    facts_array facts    = facts_from_lean_obj(lean_ctor_get(req, 3));
    str_array guides     = str_array_from_lean_obj(lean_ctor_get(req, 4));
    const char* viz_path = lean_string_cstr(lean_ctor_get(req, 5));
    lean_config cfg      = config_from_lean_obj(lean_ctor_get(req, 6));

    eqsat_result result;
    if (cfg.slotted) {
        slotted_result res = slotted_explain_congr(lhs, rhs, rws, facts, guides, cfg.rust_config, viz_path);
        result = (eqsat_result) {
            .slotted = true,
            .expl    = res.expl,
            .graph   = { .slotted = res.graph },
            .rep     = res.rep,
        };
    } else {
        egg_result res = egg_explain_congr(lhs, rhs, rws, facts, guides, cfg.rust_config, viz_path);
        result = (eqsat_result) {
            .slotted = false,
            .expl    = res.expl,
            .graph   = { .egg = res.graph },
            .rep     = res.rep,
        };
    }
    
    // TODO: Is it safe to free this?
    free_rws_array(rws);
    free(facts.ptr);
    free(guides.ptr);
    
    return result;
}

/*
structure Result.Raw where
  expl    : String
  egraph? : Option EGraph
  report? : Option Report
*/
lean_obj_res run_eqsat_request_impl(lean_obj_arg req) {
    eqsat_result result = run_eqsat_request_core(req);
    lean_object* expl   = lean_mk_string(result.expl);
    lean_object* graph  = egraph_to_lean(result.graph, result.slotted);
    lean_object* rep    = report_to_lean(result.rep);

    lean_object* lean_result = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(lean_result, 0, expl);

    if (graph == NULL) {
        lean_object* option_nil = lean_alloc_ctor(0, 0, 0); // Option.nil
        lean_ctor_set(lean_result, 1, option_nil);
        lean_ctor_set(lean_result, 2, option_nil);
    } else {
        lean_object* some_graph = lean_alloc_ctor(1, 1, 0); // Option.some
        lean_object* some_report = lean_alloc_ctor(1, 1, 0); // Option.some
        lean_ctor_set(some_graph, 0, graph);
        lean_ctor_set(some_report, 0, rep);
        lean_ctor_set(lean_result, 1, some_graph);
        lean_ctor_set(lean_result, 2, some_report);
    }

    return lean_result;
}

lean_object* run_eqsat_request(lean_obj_arg x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
    lean_obj_res res = run_eqsat_request_impl(x_1);
    lean_object* x_7; lean_object* x_8;
    x_8 = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(x_8, 0, res);
    lean_ctor_set(x_8, 1, x_6);
    return x_8;
}

extern const char* egg_query_equiv(
    egg_egraph graph,
    const char* init, 
    const char* goal
);

extern const char* slotted_query_equiv(
    slotted_egraph graph,
    const char* init, 
    const char* goal
);

lean_obj_res explain_equiv(b_lean_obj_arg graph, uint8_t slotted, lean_obj_arg init, lean_obj_arg goal) {
    const char* init_c = lean_string_cstr(init);
    const char* goal_c = lean_string_cstr(goal);
    
    if (slotted != 0) {
        slotted_egraph graph_c = to_slotted_egraph(graph);
        return lean_mk_string(slotted_query_equiv(graph_c, init_c, goal_c));
    } else {
        egg_egraph graph_c = to_egg_egraph(graph);
        return lean_mk_string(egg_query_equiv(graph_c, init_c, goal_c));
    }
}
