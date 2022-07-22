#include <boost/graph/directed_graph.hpp>
#include <cstring>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <vector>

#include "z3++.h"
#include "z3.h"

struct UserPropagate {
  Z3_context ctx;
  Z3_ast_vector assertions;
  Z3_ast_vector consequences;
  unsigned nsorts;
  std::vector<std::map<std::string, Z3_ast>> model;
  std::map<std::string, unsigned> sortIndices;
  std::map<std::string, std::map<std::string, bool>> syntacticSubsorts;
  std::vector<Z3_func_decl> funcs;
  std::vector<Z3_func_decl> variables;

  UserPropagate(Z3_context ctx)
      : ctx(ctx), consequences(Z3_mk_ast_vector(ctx)) {
    Z3_ast_vector_inc_ref(ctx, consequences);
  };

  void setAssertions(Z3_ast_vector assertions) {
    this->assertions = assertions;
  }
  void init(
      std::vector<Z3_func_decl> sorts, std::vector<Z3_func_decl> variables,
      std::vector<Z3_func_decl> params,
      std::map<std::string, std::map<std::string, bool>> syntacticSubsorts) {
    this->variables = variables;
    this->nsorts = sorts.size();
    for (auto sort : sorts) {
      funcs.push_back(sort);
    }
    for (auto variable : variables) {
      funcs.push_back(variable);
    }
    for (auto param : params) {
      funcs.push_back(param);
    }
    int nvertices = sorts.size() + variables.size() + params.size();
    model.push_back(std::map<std::string, Z3_ast>());
    for (int i = 0; i < sorts.size(); i++) {
      Z3_symbol symbol = Z3_get_decl_name(ctx, sorts[i]);
      std::string name = Z3_get_symbol_string(ctx, symbol);
      sortIndices[name] = i;
    }
    for (int i = 0, j = sorts.size(); i < variables.size(); i++, j++) {
      Z3_symbol symbol = Z3_get_decl_name(ctx, variables[i]);
      std::string name = Z3_get_symbol_string(ctx, symbol);
      sortIndices[name] = j;
    }
    for (int i = 0, j = sorts.size() + variables.size(); i < params.size();
         i++, j++) {
      Z3_symbol symbol = Z3_get_decl_name(ctx, params[i]);
      std::string name = Z3_get_symbol_string(ctx, symbol);
      sortIndices[name] = j;
    }
    this->syntacticSubsorts = syntacticSubsorts;
  }

  std::map<std::string, Z3_ast> &currentModel() { return model.back(); }
};

void split(std::string const &str, std::string const &delim,
           std::vector<std::string> &out) {
  size_t start = 0;
  size_t end;
  while ((end = str.find(delim, start)) != std::string::npos) {
    out.push_back(str.substr(start, end));
    start = end + delim.size();
  }
  out.push_back(str.substr(start));
}

void push(void *ctx, Z3_solver_callback cb) {
  UserPropagate *prop = (UserPropagate *)ctx;
  prop->model.push_back(prop->model.back());
}

void pop(void *ctx, Z3_solver_callback cb, unsigned num_scopes) {
  UserPropagate *prop = (UserPropagate *)ctx;
  for (unsigned i = 0; i < num_scopes; i++) {
    prop->model.pop_back();
  }
}

void *fresh(void *ctx, Z3_context new_context) { return ctx; }

void eq(void *ctx, Z3_solver_callback cb, Z3_ast s, Z3_ast t) {
  UserPropagate *prop = (UserPropagate *)ctx;
  Z3_app lApp = Z3_to_app(prop->ctx, s);
  Z3_app rApp = Z3_to_app(prop->ctx, t);
  Z3_func_decl lFunc = Z3_get_app_decl(prop->ctx, lApp);
  Z3_func_decl rFunc = Z3_get_app_decl(prop->ctx, rApp);
  Z3_symbol lSymbol = Z3_get_decl_name(prop->ctx, lFunc);
  Z3_symbol rSymbol = Z3_get_decl_name(prop->ctx, rFunc);
  std::string lName = Z3_get_symbol_string(prop->ctx, lSymbol);
  std::string rName = Z3_get_symbol_string(prop->ctx, rSymbol);
  int lIdx = prop->sortIndices[lName];
  int rIdx = prop->sortIndices[rName];
  if (lIdx >= prop->nsorts) {
    prop->currentModel()[lName] = t;
  }
  if (rIdx >= prop->nsorts) {
    prop->currentModel()[rName] = s;
  }
}

Z3_ast leqSortSyntax(UserPropagate *prop, Z3_ast lt, Z3_ast gt) {
  Z3_context ctx = prop->ctx;
  std::vector<Z3_ast> args;
  for (auto entry : prop->syntacticSubsorts) {
    for (auto entry2 : entry.second) {
      if (entry2.second) {
        int i = prop->sortIndices[entry.first];
        int j = prop->sortIndices[entry2.first];
        Z3_ast args2[2];
        args2[0] =
            Z3_mk_eq(ctx, lt, Z3_mk_app(ctx, prop->funcs[i], 0, nullptr));
        args2[1] =
            Z3_mk_eq(ctx, gt, Z3_mk_app(ctx, prop->funcs[j], 0, nullptr));
        args.push_back(Z3_mk_and(ctx, 2, args2));
      }
    }
  }
  return Z3_mk_or(ctx, args.size(), &args[0]);
}

void final_cb(void *ctx, Z3_solver_callback cb) {
  UserPropagate *prop = (UserPropagate *)ctx;
  Z3_solver subquery = Z3_mk_simple_solver(prop->ctx);
  Z3_solver_inc_ref(prop->ctx, subquery);
  for (unsigned i = 0; i < Z3_ast_vector_size(prop->ctx, prop->assertions);
       i++) {
    Z3_ast assertion = Z3_ast_vector_get(prop->ctx, prop->assertions, i);
    Z3_solver_assert(prop->ctx, subquery, assertion);
  }
  for (unsigned i = 0; i < Z3_ast_vector_size(prop->ctx, prop->consequences);
       i++) {
    Z3_ast assertion = Z3_ast_vector_get(prop->ctx, prop->consequences, i);
    Z3_solver_assert(prop->ctx, subquery, assertion);
  }

  std::vector<Z3_ast> distinct;
  for (Z3_func_decl variable : prop->variables) {
    Z3_symbol symbol = Z3_get_decl_name(prop->ctx, variable);
    std::string name = Z3_get_symbol_string(prop->ctx, symbol);
    Z3_ast args[2];
    args[0] = prop->currentModel()[name];
    args[1] = Z3_mk_app(prop->ctx, variable, 0, nullptr);
    Z3_solver_assert(prop->ctx, subquery,
                     leqSortSyntax(prop, args[0], args[1]));
    distinct.push_back(
        Z3_mk_not(prop->ctx, Z3_mk_eq(prop->ctx, args[0], args[1])));
  }
  Z3_solver_assert(prop->ctx, subquery,
                   Z3_mk_or(prop->ctx, distinct.size(), &distinct[0]));
  Z3_lbool result = Z3_solver_check(prop->ctx, subquery);
  if (result == Z3_L_FALSE) {
    Z3_solver_dec_ref(prop->ctx, subquery);
  } else if (result == Z3_L_TRUE) {
    Z3_model model = Z3_solver_get_model(prop->ctx, subquery);
    Z3_model_inc_ref(prop->ctx, model);

    Z3_ast_vector_resize(prop->ctx, prop->consequences, 0);
    for (Z3_func_decl variable : prop->variables) {
      Z3_ast value = Z3_model_get_const_interp(prop->ctx, model, variable);
      Z3_ast args[2];
      args[0] = value;
      args[1] = Z3_mk_app(prop->ctx, variable, 0, nullptr);
      Z3_ast conseq = leqSortSyntax(prop, args[0], args[1]);
      conseq = Z3_simplify(prop->ctx, conseq);
      Z3_solver_propagate_consequence(prop->ctx, cb, 0, nullptr, 0, nullptr,
                                      nullptr, conseq);
      Z3_ast_vector_push(prop->ctx, prop->consequences, conseq);
      // somehow creating this term makes the solver faster
      Z3_mk_not(prop->ctx, Z3_mk_eq(prop->ctx, args[0], args[1]));
    }

    Z3_solver_dec_ref(prop->ctx, subquery);
    Z3_model_dec_ref(prop->ctx, model);
  } else {
    abort();
  }
}

int main(int argc, char **argv) {
  if (argc != 6) {
    std::cout << "usage: inference <sorts> <subsorts> <syntactic subsorts> "
                 "<variables> <assertions>";
    exit(1);
  }

  Z3_context ctx = Z3_mk_context(Z3_mk_config());
  Z3_symbol sortSymbol = Z3_mk_string_symbol(ctx, "Sort");

  std::ifstream sortsS(argv[1]);
  std::string sortName;
  int nargs;
  std::vector<Z3_func_decl> sorts;
  std::vector<Z3_constructor> constructors;
  Z3_ast klabel;
  while (sortsS >> sortName >> nargs) {
    Z3_symbol sortNameSymbol = Z3_mk_string_symbol(ctx, sortName.c_str());
    std::string recognizerName = "is" + sortName;
    Z3_symbol recognizerSymbol =
        Z3_mk_string_symbol(ctx, recognizerName.c_str());
    std::vector<Z3_symbol> fieldNames;
    std::vector<Z3_sort> sortParams;
    std::vector<unsigned> sortRefs;
    for (int i = 0; i < nargs; i++) {
      abort();  // unimplemented
    }
    Z3_constructor sort =
        Z3_mk_constructor(ctx, sortNameSymbol, recognizerSymbol, nargs,
                          &fieldNames[0], 0, &sortRefs[0]);
    constructors.push_back(sort);
  }
  Z3_sort sortSort =
      Z3_mk_datatype(ctx, sortSymbol, constructors.size(), &constructors[0]);
  for (Z3_constructor sort : constructors) {
    Z3_func_decl decl;
    Z3_query_constructor(ctx, sort, 0, &decl, nullptr, nullptr);
    Z3_symbol symbol = Z3_get_decl_name(ctx, decl);
    const char *name = Z3_get_symbol_string(ctx, symbol);
    if (std::string(name) == "SortKLabel") {
      klabel = Z3_mk_app(ctx, decl, 0, nullptr);
    }
    sorts.push_back(decl);
  }

  std::map<std::string, std::map<std::string, bool>> subsorts;
  std::map<std::string, std::map<std::string, bool>> syntacticSubsorts;

  std::ifstream subsortsS(argv[2]);
  std::string line;
  while (std::getline(subsortsS, line)) {
    std::vector<std::string> parts;
    split(line, " <= ", parts);
    std::string lt = parts[0];
    std::string gt = parts[1];
    subsorts[lt][gt] = true;
  }

  std::ifstream syntacticSubsortsS(argv[3]);
  while (std::getline(syntacticSubsortsS, line)) {
    std::vector<std::string> parts;
    split(line, " <= ", parts);
    std::string lt = parts[0];
    std::string gt = parts[1];
    syntacticSubsorts[lt][gt] = true;
  }

  Z3_sort domain[2];
  domain[0] = sortSort;
  domain[1] = sortSort;
  Z3_sort boolSort = Z3_mk_bool_sort(ctx);
  Z3_symbol leqSortSymbol = Z3_mk_string_symbol(ctx, "<=Sort");
  Z3_func_decl leqSort =
      Z3_mk_func_decl(ctx, leqSortSymbol, 2, domain, boolSort);

  std::vector<Z3_ast> args;
  for (int i = 0; i < sorts.size(); i++) {
    Z3_symbol symbol1 = Z3_get_decl_name(ctx, sorts[i]);
    std::string name1 = Z3_get_symbol_string(ctx, symbol1);
    for (int j = 0; j < sorts.size(); j++) {
      Z3_symbol symbol2 = Z3_get_decl_name(ctx, sorts[j]);
      std::string name2 = Z3_get_symbol_string(ctx, symbol2);
      if (subsorts[name1][name2]) {
        Z3_ast args2[2];
        args2[0] = Z3_mk_eq(ctx, Z3_mk_bound(ctx, 0, sortSort),
                            Z3_mk_app(ctx, sorts[i], 0, nullptr));
        args2[1] = Z3_mk_eq(ctx, Z3_mk_bound(ctx, 1, sortSort),
                            Z3_mk_app(ctx, sorts[j], 0, nullptr));
        args.push_back(Z3_mk_and(ctx, 2, args2));
      }
    }
  }
  Z3_ast leqSortExp = Z3_mk_or(ctx, args.size(), &args[0]);

  Z3_solver solver = Z3_mk_simple_solver(ctx);
  Z3_solver_inc_ref(ctx, solver);
  UserPropagate *propagate = new UserPropagate(ctx);
  Z3_solver_propagate_init(ctx, solver, propagate, push, pop, fresh);
  Z3_solver_propagate_final(ctx, solver, final_cb);
  Z3_solver_propagate_eq(ctx, solver, eq);
  for (Z3_func_decl decl : sorts) {
    Z3_solver_propagate_register(ctx, solver, Z3_mk_app(ctx, decl, 0, nullptr));
  }

  std::vector<Z3_func_decl> variables, params;
  bool isParam = true;

  std::vector<Z3_symbol> smtDeclNames;
  std::vector<Z3_func_decl> smtDecls;
  smtDeclNames.push_back(leqSortSymbol);
  smtDecls.push_back(leqSort);

  std::ifstream variablesS(argv[4]);
  while (std::getline(variablesS, line)) {
    if (line.empty()) {
      isParam = false;
      continue;
    }
    Z3_symbol varSymbol = Z3_mk_string_symbol(ctx, line.c_str());
    smtDeclNames.push_back(varSymbol);
    Z3_func_decl decl = Z3_mk_func_decl(ctx, varSymbol, 0, nullptr, sortSort);
    Z3_ast _const = Z3_mk_app(ctx, decl, 0, nullptr);
    Z3_solver_propagate_register(ctx, solver, _const);
    smtDecls.push_back(decl);
    if (isParam) {
      params.push_back(decl);
    } else {
      variables.push_back(decl);
    }
  }

  propagate->init(sorts, variables, params, syntacticSubsorts);

  for (Z3_func_decl param : params) {
    Z3_ast app = Z3_mk_app(ctx, param, 0, nullptr);
    Z3_ast eq = Z3_mk_eq(ctx, app, klabel);
    Z3_ast _not = Z3_mk_not(ctx, eq);
    Z3_solver_assert(ctx, solver, _not);
  }

  std::vector<Z3_symbol> smtSortNames;
  smtSortNames.push_back(sortSymbol);
  std::vector<Z3_sort> smtSorts;
  smtSorts.push_back(sortSort);
  Z3_ast_vector constraints =
      Z3_parse_smtlib2_file(ctx, argv[5], 1, &smtSortNames[0], &smtSorts[0],
                            smtDecls.size(), &smtDeclNames[0], &smtDecls[0]);
  Z3_ast_vector_inc_ref(ctx, constraints);
  Z3_ast constraint = Z3_ast_vector_get(ctx, constraints, 0);
  constraint = Z3_substitute_funs(ctx, constraint, 1, &leqSort, &leqSortExp);
  Z3_solver_assert(ctx, solver, constraint);

  Z3_ast_vector assertions = Z3_solver_get_assertions(ctx, solver);
  Z3_ast_vector_inc_ref(ctx, assertions);
  propagate->setAssertions(assertions);

  Z3_lbool result = Z3_solver_check(ctx, solver);
  std::cout << result << std::endl;
  if (result == Z3_L_TRUE) {
    Z3_model model = Z3_solver_get_model(ctx, solver);
    Z3_model_inc_ref(ctx, model);
    for (Z3_func_decl variable : variables) {
      Z3_ast value = Z3_model_get_const_interp(ctx, model, variable);
      Z3_symbol name = Z3_get_decl_name(ctx, variable);
      std::string s = Z3_get_symbol_string(ctx, name);
      std::cout << s << " -> " << Z3_ast_to_string(ctx, value) << std::endl;
    }
  }

  return 0;
}
