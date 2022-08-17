#include <boost/graph/directed_graph.hpp>
#include <cstring>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <vector>

#include "z3++.h"
#include "z3.h"

class Node {
  Z3_ast term, value;
  unsigned id;
  Node *root;
  unsigned size;
  Z3_context ctx;

  friend class UnionFind;
  friend bool operator==(const Node &lhs, const Node &rhs);
  friend bool operator!=(const Node &lhs, const Node &rhs);

  Node(Z3_context ctx, Z3_ast a) {
    this->ctx = ctx;
    this->term = a;
    this->id = Z3_get_ast_id(ctx, a);
    this->root = this;
    this->size = 1;
    this->value = nullptr;
  }

  void print() {
    if (value) {
      std::cout << Z3_ast_to_string(ctx, term) << " = "
                << Z3_ast_to_string(ctx, value) << std::endl;
    }
  }
};

Z3_context global_ctx;

bool operator==(const Node &lhs, const Node &rhs) { return lhs.id == rhs.id; }

bool operator!=(const Node &lhs, const Node &rhs) { return lhs.id != rhs.id; }

class UnionFind {
  Z3_context ctx;
  std::vector<Node *> nodes;
  std::vector<std::function<void(void)>> *trail;

 public:
  UnionFind(Z3_context ctx, std::vector<std::function<void(void)>> *trail)
      : ctx(ctx), trail(trail) {}

  Node *node(Z3_ast a) {
    unsigned id = Z3_get_ast_id(ctx, a);
    Node *n;
    if (id < nodes.size()) {
      n = nodes[id];
      if (n) {
        return n;
      }
    } else {
      nodes.resize(id + 1);
    }
    n = new Node(ctx, a);
    nodes[id] = n;
    trail->push_back([this, id]() { this->nodes[id] = nullptr; });
    return n;
  }

  void merge(Z3_ast aast, Z3_ast bast) {
    Node *a = node(aast);
    Node *b = node(bast);
    a = find(a);
    b = find(b);
    if (*a == *b) {
      return;
    }
    if (a->size < b->size) {
      std::swap(a, b);
    }
    if (a->value && b->value) {
      abort();
    }
    Z3_ast value = a->value;
    if (b->value) {
      value = b->value;
    }
    Node *old_root = b->root;
    unsigned old_asize = a->size;
    Z3_ast old_bvalue = b->value;
    Z3_ast old_avalue = a->value;
    b->root = a->root;
    b->value = value;
    a->value = value;
    a->size += b->size;
    trail->push_back([b, a, old_root, old_asize, old_bvalue, old_avalue]() {
      b->root = old_root;
      a->size = old_asize;
      b->value = old_bvalue;
      a->value = old_avalue;
    });
  }

  Node *find(Node *a) {
    Node *root = a->root;
    while (root != root->root) {
      root = root->root;
    }
    while (a != root) {
      Node *newroot = a->root;
      a->root = root;
      a = newroot;
    }
    return root;
  }

  void set_value(Z3_ast a) {
    Node *n = find(node(a));
    if (n->value) {
      return;
    }
    n->value = a;
    trail->push_back([n]() { n->value = nullptr; });
  }

  Z3_ast get_value(Z3_ast a) { return find(node(a))->value; }

  Z3_ast root_term(Z3_ast a) { return find(node(a))->term; }

  void print() {
    for (auto node : nodes) {
      if (node) {
        node->print();
      }
    }
  }
};

class Graph {
 private:
  std::vector<std::vector<bool>> out_edges;
  std::vector<std::vector<std::vector<Z3_ast>>> labels;
  std::vector<std::set<unsigned>> out_adjacent;
  std::vector<std::set<unsigned>> in_edges;
  std::vector<std::function<void(void)>> *trail;

 public:
  Graph(unsigned size, std::vector<std::function<void(void)>> *trail) {
    this->trail = trail;
    for (unsigned i = 0; i < size; i++) {
      in_edges.push_back(std::set<unsigned>());
      out_adjacent.push_back(std::set<unsigned>());
      out_edges.push_back(std::vector<bool>(size));
      labels.push_back(std::vector<std::vector<Z3_ast>>(size));
    }
  }

  void add_edge(unsigned from, unsigned to, std::vector<Z3_ast> const &label) {
    unsigned oldsize = label.size();
    if (out_edges[from][to]) {
      labels[from][to].insert(labels[from][to].end(), label.begin(),
                              label.end());
      trail->push_back([this, oldsize, from, to]() {
        for (unsigned i = 0; i < oldsize; i++) {
          labels[from][to].pop_back();
        }
      });
      return;
    }
    out_edges[from][to] = true;
    in_edges[to].insert(from);
    out_adjacent[from].insert(to);
    labels[from][to].insert(labels[from][to].end(), label.begin(), label.end());
    trail->push_back([this, oldsize, from, to]() {
      out_edges[from][to] = false;
      in_edges[to].erase(from);
      out_adjacent[from].erase(to);
      for (unsigned i = 0; i < oldsize; i++) {
        labels[from][to].pop_back();
      }
    });
  }

  void add_edge_transitive(unsigned from, unsigned to, Z3_ast label) {
    if (from != to) {
      for (unsigned in_edge : in_edges[from]) {
        std::vector<Z3_ast> lbl = get_label(in_edge, from);
        lbl.push_back(label);
        add_edge(in_edge, to, lbl);
      }
      for (unsigned out_edge : out_adjacent[to]) {
        std::vector<Z3_ast> lbl = get_label(to, out_edge);
        lbl.push_back(label);
        add_edge(from, out_edge, lbl);
      }
    }
    std::vector<Z3_ast> lbl;
    lbl.push_back(label);
    add_edge(from, to, lbl);
  }

  bool has_edge(unsigned from, unsigned to) const {
    return out_edges[from][to];
  }

  std::vector<Z3_ast> get_label(unsigned from, unsigned to) const {
    return labels[from][to];
  }

  void add_vertex() {
    for (int i = 0; i < out_edges.size(); i++) {
      out_edges[i].push_back(false);
      labels[i].push_back(std::vector<Z3_ast>());
    }
    out_edges.push_back(std::vector<bool>(out_edges.size() + 1));
    labels.push_back(std::vector<std::vector<Z3_ast>>(labels.size() + 1));
    in_edges.push_back(std::set<unsigned>());
    out_adjacent.push_back(std::set<unsigned>());
  }

  void clear() {
    for (int i = 0; i < out_edges.size(); i++) {
      for (int j = 0; j < out_edges[i].size(); j++) {
        out_edges[i][j] = false;
        labels[i][j].clear();
      }
      in_edges[i].clear();
      out_adjacent[i].clear();
    }
  }
};

struct UserPropagate {
  Z3_context ctx;
  std::vector<unsigned> limit;
  std::vector<std::function<void(void)>> trail;
  Z3_func_decl leqSort, leqSortSyntax;
  UnionFind uf;
  std::vector<std::vector<bool>> subsorts, syntacticSubsorts;
  std::vector<std::vector<Z3_ast>> fixedNotSubsorts, fixedNotSyntacticSubsorts;
  std::vector<unsigned> idToIdx;
  std::vector<bool> minSortsLeq, minSortsLeqSyntax, maxSortsLeq,
      maxSortsLeqSyntax;
  std::vector<std::pair<Z3_ast, Z3_ast>> fixedLeqSort, fixedLeqSortSyntax;
  std::vector<Z3_func_decl> sorts, variables, params;
  unsigned maxId;
  bool first, fresh;
  Graph fixedSubsorts;
  Graph fixedSyntacticSubsorts;
  unsigned nvertices;
  Z3_ast_vector assertions;
  Z3_ast_vector consequences;
  // unsigned nsorts;
  // std::vector<std::map<std::string, Z3_ast>> model;
  // std::map<std::string, unsigned> sortIndices;
  // std::map<std::string, std::map<std::string, bool>> syntacticSubsorts;
  // std::vector<Z3_func_decl> funcs;
  // std::vector<Z3_func_decl> variables;

  UserPropagate(Z3_context ctx, unsigned nvertices, bool fresh)
      : ctx(ctx),
        uf(ctx, &trail),
        first(true),
        fresh(fresh),
        nvertices(nvertices),
        fixedSubsorts(nvertices, &trail),
        fixedSyntacticSubsorts(nvertices, &trail),
        consequences(Z3_mk_ast_vector(ctx)) {
    Z3_ast_vector_inc_ref(ctx, consequences);
  }

  void fixedTrail(Z3_solver_callback cb, Z3_ast x, Z3_ast v,
                  std::vector<std::vector<bool>> const &table, Graph &fixedTrue,
                  std::vector<std::vector<Z3_ast>> &fixedFalse,
                  std::vector<bool> const &minSorts,
                  std::vector<bool> const &maxSorts,
                  std::vector<std::pair<Z3_ast, Z3_ast>> &trail) {
    if (checkConflict(cb, x, v, table, fixedTrue, fixedFalse, minSorts,
                      maxSorts, false)) {
      return;
    }
    trail.push_back(std::make_pair(x, v));
    Z3_lbool value = Z3_get_bool_value(ctx, v);
    Z3_app app = Z3_to_app(ctx, x);
    Z3_ast a = Z3_get_app_arg(ctx, app, 0);
    Z3_ast b = Z3_get_app_arg(ctx, app, 1);
    unsigned aid = Z3_get_ast_id(ctx, a);
    unsigned bid = Z3_get_ast_id(ctx, b);
    Z3_ast va = uf.get_value(a);
    Z3_ast vb = uf.get_value(b);
    if (!va || !vb) {
      if (value == Z3_L_TRUE) {
        fixedTrue.add_edge_transitive(idToIdx[aid], idToIdx[bid], x);
      } else if (value == Z3_L_FALSE) {
        Z3_ast oldval = fixedFalse[idToIdx[aid]][idToIdx[bid]];
        fixedFalse[idToIdx[aid]][idToIdx[bid]] = x;
        this->trail.push_back([&fixedFalse, this, oldval, aid, bid]() {
          fixedFalse[idToIdx[aid]][idToIdx[bid]] = oldval;
        });
      } else {
        abort();
      }
    }
    this->trail.push_back([&trail]() { trail.pop_back(); });
  }

  bool checkConflict(Z3_solver_callback cb, Z3_ast x, Z3_ast v,
                     std::vector<std::vector<bool>> const &table,
                     Graph const &fixedTrue,
                     std::vector<std::vector<Z3_ast>> const &fixedFalse,
                     std::vector<bool> const &minSorts,
                     std::vector<bool> const &maxSorts, bool isFinal) {
    Z3_app app = Z3_to_app(ctx, x);
    Z3_ast a = Z3_get_app_arg(ctx, app, 0);
    Z3_ast b = Z3_get_app_arg(ctx, app, 1);
    Z3_ast va = uf.get_value(a);
    Z3_ast vb = uf.get_value(b);
    Z3_lbool value = Z3_get_bool_value(ctx, v);
    // if (va && a != va && isFinal) {
    // std::cout << "assigned: " << Z3_ast_to_string(ctx, a) << " "
    //          << Z3_ast_to_string(ctx, va) << std::endl;
    //}
    // if (vb && b != vb && isFinal) {
    // std::cout << "assigned: " << Z3_ast_to_string(ctx, b) << " "
    //          << Z3_ast_to_string(ctx, vb) << std::endl;
    //}
    if (!va || !vb) {
      // if (isFinal) {
      //  std::cout << "unassigned: " << Z3_ast_to_string(ctx, x) << " "
      //            << Z3_ast_to_string(ctx, v) << std::endl;
      // abort();
      //}
      unsigned aid, bid;
      Z3_ast lhs[2], rhs[2];
      unsigned neqs = 0;
      if (va) {
        aid = Z3_get_ast_id(ctx, va);
        lhs[0] = a;
        rhs[0] = va;
        neqs++;
        if (value == Z3_L_FALSE && maxSorts[idToIdx[aid]]) {
          // std::cout << "conflict: ! " << Z3_ast_to_string(ctx, x) <<
          // std::endl;
          Z3_solver_propagate_consequence(ctx, cb, 1, &x, 1, &a, &va,
                                          Z3_mk_false(ctx));
          return true;
        }
      } else {
        aid = Z3_get_ast_id(ctx, a);
      }
      if (vb) {
        bid = Z3_get_ast_id(ctx, vb);
        lhs[neqs] = b;
        rhs[neqs] = vb;
        neqs++;
        if (value == Z3_L_TRUE && minSorts[idToIdx[bid]]) {
          // std::cout << "propagating eq: " << Z3_ast_to_string(ctx, a) << " "
          //<< Z3_ast_to_string(ctx, vb) << std::endl;
          Z3_solver_propagate_consequence(ctx, cb, 1, &x, 1, &b, &vb,
                                          Z3_mk_eq(ctx, a, vb));
        }
      } else {
        bid = Z3_get_ast_id(ctx, b);
      }
      if (value == Z3_L_TRUE) {
        if (auto fixed = fixedFalse[idToIdx[aid]][idToIdx[bid]]) {
          Z3_ast args[2];
          args[0] = x;
          args[1] = fixed;
          // std::cout << "conflict: " << Z3_ast_to_string(ctx, x) << std::endl;
          Z3_solver_propagate_consequence(ctx, cb, 2, args, neqs, lhs, rhs,
                                          Z3_mk_false(ctx));
          return true;
        }
      } else if (value == Z3_L_FALSE) {
        if (fixedTrue.has_edge(idToIdx[aid], idToIdx[bid])) {
          // std::cout << "conflict: ! " << Z3_ast_to_string(ctx, x) <<
          // std::endl;
          std::vector<Z3_ast> label =
              fixedTrue.get_label(idToIdx[aid], idToIdx[bid]);
          label.push_back(x);
          Z3_solver_propagate_consequence(ctx, cb, label.size(), &label[0],
                                          neqs, lhs, rhs, Z3_mk_false(ctx));
          return true;
        }
      } else {
        abort();
      }
      return false;
    }
    unsigned aid = Z3_get_ast_id(ctx, va);
    unsigned bid = Z3_get_ast_id(ctx, vb);
    if (value == Z3_L_TRUE) {
      if (!table[idToIdx[aid]][idToIdx[bid]]) {
        Z3_ast lhs[2], rhs[2];
        lhs[0] = a;
        lhs[1] = b;
        rhs[0] = va;
        rhs[1] = vb;
        // std::cout << "conflict: " << Z3_ast_to_string(ctx, x) << std::endl;
        Z3_solver_propagate_consequence(ctx, cb, 1, &x, 2, lhs, rhs,
                                        Z3_mk_false(ctx));
        return true;
      } else {
        return false;
      }
    } else if (value == Z3_L_FALSE) {
      if (table[idToIdx[aid]][idToIdx[bid]]) {
        Z3_ast lhs[2], rhs[2];
        lhs[0] = a;
        lhs[1] = b;
        rhs[0] = va;
        rhs[1] = vb;
        // std::cout << "conflict: ! " << Z3_ast_to_string(ctx, x) << std::endl;
        Z3_solver_propagate_consequence(ctx, cb, 1, &x, 2, lhs, rhs,
                                        Z3_mk_false(ctx));
        return true;
      } else {
        return false;
      }
    } else {
      abort();
    }
  }

  bool checkFinal(Z3_solver_callback cb,
                  std::vector<std::pair<Z3_ast, Z3_ast>> asserted,
                  std::vector<std::vector<bool>> const &table,
                  Graph const &fixedTrue,
                  std::vector<std::vector<Z3_ast>> const &fixedFalse,
                  std::vector<bool> const &minSorts,
                  std::vector<bool> const &maxSorts) {
    // for (auto entry : asserted) {
    //  std::cout << "fixed: " << Z3_ast_to_string(ctx, entry.first) << " "
    //            << Z3_ast_to_string(ctx, entry.second) << std::endl;
    //}
    // std::cout << std::endl;
    for (auto entry : asserted) {
      if (checkConflict(cb, entry.first, entry.second, table, fixedTrue,
                        fixedFalse, minSorts, maxSorts, true)) {
        return true;
      }
    }
    return false;
  }

  void setAssertions(Z3_ast_vector assertions) {
    this->assertions = assertions;
  }

  void reset() {
    limit.clear();
    trail.clear();
    uf = UnionFind(ctx, &trail);
    fixedLeqSort.clear();
    fixedLeqSortSyntax.clear();
    fixedSubsorts.clear();
    fixedSyntacticSubsorts.clear();
    fixedNotSubsorts.clear();
    fixedNotSyntacticSubsorts.clear();
    for (int i = 0; i < nvertices; i++) {
      fixedNotSubsorts.push_back(std::vector<Z3_ast>(nvertices));
      fixedNotSyntacticSubsorts.push_back(std::vector<Z3_ast>(nvertices));
    }
  }

  void initId(Z3_ast a) {
    unsigned id = Z3_get_ast_id(ctx, a);
    if (id <= maxId) {
      return;
    }
    unsigned idx = nvertices;
    fixedSubsorts.add_vertex();
    fixedSyntacticSubsorts.add_vertex();
    for (unsigned i = 0; i < nvertices; i++) {
      fixedNotSubsorts[i].push_back(nullptr);
      fixedNotSyntacticSubsorts[i].push_back(nullptr);
    }
    fixedNotSubsorts.push_back(std::vector<Z3_ast>(nvertices + 1));
    fixedNotSyntacticSubsorts.push_back(std::vector<Z3_ast>(nvertices + 1));
    if (id >= idToIdx.size()) {
      idToIdx.resize(id + 1);
    }
    idToIdx[id] = nvertices;
    nvertices++;
  }

  void initGraph(std::vector<std::vector<bool>> table, Graph &fixedTrue) {
    for (int i = 0; i < table.size(); i++) {
      for (int j = 0; j < table[i].size(); j++) {
        if (table[i][j]) {
          fixedTrue.add_edge(i, j, std::vector<Z3_ast>());
        }
      }
    }
  }

  void init(std::vector<Z3_func_decl> sorts,
            std::vector<Z3_func_decl> variables,
            std::vector<Z3_func_decl> params,
            std::vector<std::vector<bool>> subsorts,
            std::vector<std::vector<bool>> syntacticSubsorts,
            std::vector<bool> minSortsLeq, std::vector<bool> minSortsLeqSyntax,
            std::vector<bool> maxSortsLeq, std::vector<bool> maxSortsLeqSyntax,
            std::vector<unsigned> idToIdx, Z3_func_decl leqSort,
            Z3_func_decl leqSortSyntax) {
    this->leqSort = leqSort;
    this->leqSortSyntax = leqSortSyntax;
    this->sorts = sorts;
    this->variables = variables;
    this->params = params;
    this->subsorts = subsorts;
    this->syntacticSubsorts = syntacticSubsorts;
    this->idToIdx = idToIdx;
    this->maxId = idToIdx.size() - 1;
    this->minSortsLeq = minSortsLeq;
    this->minSortsLeqSyntax = minSortsLeqSyntax;
    this->maxSortsLeq = maxSortsLeq;
    this->maxSortsLeqSyntax = maxSortsLeqSyntax;
    for (Z3_func_decl sort : sorts) {
      uf.set_value(Z3_mk_app(ctx, sort, 0, nullptr));
    }
    initGraph(subsorts, fixedSubsorts);
    initGraph(syntacticSubsorts, fixedSyntacticSubsorts);
    for (int i = 0; i < nvertices; i++) {
      fixedNotSubsorts.push_back(std::vector<Z3_ast>(nvertices));
      fixedNotSyntacticSubsorts.push_back(std::vector<Z3_ast>(nvertices));
    }
    /*
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
    */
  }
  /*
    std::map<std::string, Z3_ast> &currentModel() { return model.back(); }
    */
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
  // std::cout << "push" << std::endl;
  UserPropagate *prop = (UserPropagate *)ctx;
  prop->limit.push_back(prop->trail.size());
}

void pop(void *ctx, Z3_solver_callback cb, unsigned num_scopes) {
  // std::cout << "pop " << num_scopes << std::endl;
  UserPropagate *prop = (UserPropagate *)ctx;
  unsigned head = prop->limit[prop->limit.size() - num_scopes];
  while (prop->trail.size() > head) {
    prop->trail.back()();
    prop->trail.pop_back();
  }
  prop->limit.resize(prop->limit.size() - num_scopes);
}

void *fresh(void *ctx, Z3_context new_context) {
  abort();
  /*
  std::cout << "fresh" << std::endl;
  UserPropagate *prop = (UserPropagate *)ctx;
  auto retval = new UserPropagate(new_context, prop->nvertices);
  retval->init(prop->sorts, prop->variables, prop->params, prop->subsorts,
               prop->syntacticSubsorts, prop->minSortsLeq,
               prop->minSortsLeqSyntax, prop->maxSortsLeq,
               prop->maxSortsLeqSyntax, prop->idToIdx, prop->leqSort,
               prop->leqSortSyntax);
  return retval;*/
}

void fixed(void *ctx, Z3_solver_callback cb, Z3_ast x, Z3_ast v) {
  UserPropagate *prop = (UserPropagate *)ctx;
  // std::cout << "fixed: " << Z3_ast_to_string(prop->ctx, x) << " "
  //          << Z3_ast_to_string(prop->ctx, v) << std::endl;
  Z3_app app = Z3_to_app(prop->ctx, x);
  Z3_func_decl decl = Z3_get_app_decl(prop->ctx, app);
  if (decl == prop->leqSort) {
    prop->fixedTrail(cb, x, v, prop->subsorts, prop->fixedSubsorts,
                     prop->fixedNotSubsorts, prop->minSortsLeq,
                     prop->maxSortsLeq, prop->fixedLeqSort);
  } else if (decl == prop->leqSortSyntax) {
    prop->fixedTrail(cb, x, v, prop->syntacticSubsorts,
                     prop->fixedSyntacticSubsorts,
                     prop->fixedNotSyntacticSubsorts, prop->minSortsLeqSyntax,
                     prop->maxSortsLeqSyntax, prop->fixedLeqSortSyntax);
  }
}

void created(void *ctx, Z3_solver_callback cb, Z3_ast t) {
  UserPropagate *prop = (UserPropagate *)ctx;
  Z3_solver_propagate_register_cb(prop->ctx, cb, t);
  Z3_app app = Z3_to_app(prop->ctx, t);
  Z3_ast x = Z3_get_app_arg(prop->ctx, app, 0);
  Z3_ast y = Z3_get_app_arg(prop->ctx, app, 1);
  prop->initId(x);
  prop->initId(y);
  Z3_solver_propagate_register_cb(prop->ctx, cb, x);
  Z3_solver_propagate_register_cb(prop->ctx, cb, y);
  if (prop->first) {
    for (Z3_func_decl sort : prop->sorts) {
      Z3_solver_propagate_register_cb(prop->ctx, cb,
                                      Z3_mk_app(prop->ctx, sort, 0, nullptr));
    }
    prop->first = false;
  }
}

void eq(void *ctx, Z3_solver_callback cb, Z3_ast s, Z3_ast t) {
  UserPropagate *prop = (UserPropagate *)ctx;
  // std::cout << "eq: " << Z3_ast_to_string(prop->ctx, s) << " "
  //          << Z3_ast_to_string(prop->ctx, t) << std::endl;
  prop->uf.merge(s, t);
}

void final_cb(void *ctx, Z3_solver_callback cb) {
  // std::cout << "final" << std::endl;
  UserPropagate *prop = (UserPropagate *)ctx;
  if (prop->checkFinal(cb, prop->fixedLeqSortSyntax, prop->syntacticSubsorts,
                       prop->fixedSyntacticSubsorts,
                       prop->fixedNotSyntacticSubsorts, prop->minSortsLeqSyntax,
                       prop->maxSortsLeqSyntax)) {
    return;
  }
  if (prop->checkFinal(cb, prop->fixedLeqSort, prop->subsorts,
                       prop->fixedSubsorts, prop->fixedNotSubsorts,
                       prop->minSortsLeq, prop->maxSortsLeq)) {
    return;
  }

  // std::cout << "solution" << std::endl;
  // prop->uf.print();
  if (prop->fresh) {
    return;
  }

  Z3_solver subquery = Z3_mk_simple_solver(prop->ctx);
  Z3_solver_inc_ref(prop->ctx, subquery);
  UserPropagate *propagate =
      new UserPropagate(prop->ctx, prop->nvertices, true);
  Z3_solver_propagate_init(prop->ctx, subquery, propagate, push, pop, fresh);
  Z3_solver_propagate_final(prop->ctx, subquery, final_cb);
  Z3_solver_propagate_fixed(prop->ctx, subquery, fixed);
  Z3_solver_propagate_created(prop->ctx, subquery, created);
  Z3_solver_propagate_eq(prop->ctx, subquery, eq);
  propagate->init(prop->sorts, prop->variables, prop->params, prop->subsorts,
                  prop->syntacticSubsorts, prop->minSortsLeq,
                  prop->minSortsLeqSyntax, prop->maxSortsLeq,
                  prop->maxSortsLeqSyntax, prop->idToIdx, prop->leqSort,
                  prop->leqSortSyntax);
  propagate->setAssertions(prop->assertions);

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
    args[1] = Z3_mk_app(prop->ctx, variable, 0, nullptr);
    args[0] = prop->uf.get_value(args[1]);
    if (!args[0]) {
      continue;
    }
    Z3_solver_assert(prop->ctx, subquery,
                     Z3_mk_app(prop->ctx, prop->leqSortSyntax, 2, args));
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
      Z3_ast conseq = Z3_mk_app(prop->ctx, prop->leqSortSyntax, 2, args);
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

/*
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
*/

void initIds(Z3_context ctx, std::vector<Z3_func_decl> decls, unsigned idx,
             unsigned off, std::vector<unsigned> &idToIdx) {
  Z3_func_decl s = decls[idx];
  unsigned id = Z3_get_ast_id(ctx, Z3_mk_app(ctx, s, 0, nullptr));
  if (id >= idToIdx.size()) {
    idToIdx.resize(id + 1);
  }
  idToIdx[id] = idx + off;
}

std::map<std::string, std::set<std::string>> rtc(
    std::vector<std::string> const &sortNames,
    std::map<std::string, std::set<std::string>> &binaryRelation) {
  std::map<std::string, std::set<std::string>> step = binaryRelation;
  std::map<std::string, std::set<std::string>> result;
  for (std::string sort : sortNames) {
    result[sort].insert(sort);
  }
  bool change = true;
  while (change) {
    change = false;
    for (auto &entry : result) {
      std::set<std::string> sorts = entry.second;
      for (auto sort1 : sorts) {
        for (auto sort2 : step[sort1]) {
          entry.second.insert(sort2);
        }
      }
      if (entry.second.size() > sorts.size()) {
        change = true;
      }
    }
  }
  return result;
}

int main(int argc, char **argv) {
  if (argc != 6) {
    std::cout << "usage: inference <sorts> <subsorts> <syntactic subsorts> "
                 "<variables> <assertions>";
    exit(1);
  }

  Z3_context ctx = Z3_mk_context(Z3_mk_config());
  global_ctx = ctx;
  Z3_symbol sortSymbol = Z3_mk_string_symbol(ctx, "Sort");

  std::ifstream sortsS(argv[1]);
  std::string sortName;
  int nargs;
  std::vector<Z3_func_decl> sorts;
  std::vector<std::string> sortNames;
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
    sortNames.push_back(name);
  }

  std::map<std::string, std::set<std::string>> subsorts;
  std::map<std::string, std::set<std::string>> syntacticSubsorts;

  std::ifstream subsortsS(argv[2]);
  std::string line;
  while (std::getline(subsortsS, line)) {
    std::vector<std::string> parts;
    split(line, " <= ", parts);
    std::string lt = parts[0];
    std::string gt = parts[1];
    subsorts[gt].insert(lt);
  }

  std::ifstream syntacticSubsortsS(argv[3]);
  while (std::getline(syntacticSubsortsS, line)) {
    std::vector<std::string> parts;
    split(line, " <= ", parts);
    std::string lt = parts[0];
    std::string gt = parts[1];
    syntacticSubsorts[gt].insert(lt);
  }

  std::map<std::string, std::set<std::string>> rtcSubsorts =
                                                   rtc(sortNames, subsorts),
                                               rtcSyntacticSubsorts =
                                                   rtc(sortNames,
                                                       syntacticSubsorts);

  Z3_sort domain[2];
  domain[0] = sortSort;
  domain[1] = sortSort;
  Z3_sort boolSort = Z3_mk_bool_sort(ctx);
  Z3_symbol leqSortSymbol = Z3_mk_string_symbol(ctx, "<=Sort");
  Z3_func_decl leqSort =
      Z3_solver_propagate_declare(ctx, leqSortSymbol, 2, domain, boolSort);
  Z3_symbol leqSortSyntaxSymbol = Z3_mk_string_symbol(ctx, "<=SortSyntax");
  Z3_func_decl leqSortSyntax = Z3_solver_propagate_declare(
      ctx, leqSortSyntaxSymbol, 2, domain, boolSort);
  /*
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
  */
  // for (Z3_func_decl decl : sorts) {
  //  Z3_solver_propagate_register(ctx, solver, Z3_mk_app(ctx, decl, 0,
  //  nullptr));
  // }

  std::vector<Z3_func_decl> variables, params;
  bool isParam = true;

  std::vector<Z3_symbol> smtDeclNames;
  std::vector<Z3_func_decl> smtDecls;
  smtDeclNames.push_back(leqSortSymbol);
  smtDeclNames.push_back(leqSortSyntaxSymbol);
  smtDecls.push_back(leqSort);
  smtDecls.push_back(leqSortSyntax);

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
    // Z3_solver_propagate_register(ctx, solver, _const);
    smtDecls.push_back(decl);
    if (isParam) {
      params.push_back(decl);
    } else {
      variables.push_back(decl);
    }
  }

  Z3_solver solver = Z3_mk_simple_solver(ctx);
  Z3_solver_inc_ref(ctx, solver);
  UserPropagate *propagate = new UserPropagate(
      ctx, sorts.size() + variables.size() + params.size(), false);
  Z3_solver_propagate_init(ctx, solver, propagate, push, pop, fresh);
  Z3_solver_propagate_final(ctx, solver, final_cb);
  Z3_solver_propagate_fixed(ctx, solver, fixed);
  Z3_solver_propagate_created(ctx, solver, created);
  Z3_solver_propagate_eq(ctx, solver, eq);

  std::vector<std::vector<bool>> subsortsZ3, syntacticSubsortsZ3;
  for (int i = 0; i < sorts.size(); i++) {
    subsortsZ3.push_back(std::vector<bool>(sorts.size()));
    syntacticSubsortsZ3.push_back(std::vector<bool>(sorts.size()));
  }
  std::vector<bool> minSortsLeq(sorts.size()), minSortsLeqSyntax(sorts.size()),
      maxSortsLeq(sorts.size()), maxSortsLeqSyntax(sorts.size());

  std::vector<unsigned> idToIdx;
  for (int idx = 0; idx < sorts.size(); idx++) {
    initIds(ctx, sorts, idx, 0, idToIdx);
  }
  for (int idx = 0; idx < variables.size(); idx++) {
    initIds(ctx, variables, idx, sorts.size(), idToIdx);
  }
  for (int idx = 0; idx < params.size(); idx++) {
    initIds(ctx, params, idx, sorts.size() + params.size(), idToIdx);
  }

  for (int i = 0; i < sorts.size(); i++) {
    Z3_func_decl s1 = sorts[i];
    Z3_symbol symbol1 = Z3_get_decl_name(ctx, s1);
    std::string name1 = Z3_get_symbol_string(ctx, symbol1);
    for (int j = 0; j < sorts.size(); j++) {
      Z3_func_decl s2 = sorts[j];
      Z3_symbol symbol2 = Z3_get_decl_name(ctx, s2);
      std::string name2 = Z3_get_symbol_string(ctx, symbol2);
      Z3_ast args[2];
      args[0] = Z3_mk_app(ctx, s1, 0, nullptr);
      args[1] = Z3_mk_app(ctx, s2, 0, nullptr);
      if (subsorts[name2].count(name1)) {
        Z3_solver_assert(ctx, solver, Z3_mk_app(ctx, leqSort, 2, args));
        //} else {
        //  Z3_solver_assert(ctx, solver,
        //                   Z3_mk_not(ctx, Z3_mk_app(ctx, leqSort, 2,
        //                   args)));
      }
      if (rtcSubsorts[name2].count(name1)) {
        subsortsZ3[i][j] = true;
      }
      if (syntacticSubsorts[name2].count(name1)) {
        Z3_solver_assert(ctx, solver, Z3_mk_app(ctx, leqSortSyntax, 2, args));
        //} else {
        //  Z3_solver_assert(
        //      ctx, solver,
        //      Z3_mk_not(ctx, Z3_mk_app(ctx, leqSortSyntax, 2, args)));
      }
      if (rtcSyntacticSubsorts[name2].count(name1)) {
        syntacticSubsortsZ3[i][j] = true;
      }
    }
  }

  for (int i = 0; i < sorts.size(); i++) {
    Z3_func_decl s = sorts[i];
    Z3_symbol symbol = Z3_get_decl_name(ctx, s);
    std::string name = Z3_get_symbol_string(ctx, symbol);
    if (rtcSubsorts[name].size() == 1) {
      minSortsLeq[i] = true;
    }
    if (rtcSyntacticSubsorts[name].size() == 1) {
      minSortsLeqSyntax[i] = true;
    }
  }

  for (int i = 0; i < sorts.size(); i++) {
    bool maxLeq = true, maxLeqSyntax = true;
    Z3_func_decl s1 = sorts[i];
    Z3_symbol symbol1 = Z3_get_decl_name(ctx, s1);
    std::string name1 = Z3_get_symbol_string(ctx, symbol1);
    for (int j = 0; j < sorts.size(); j++) {
      if (i == j) {
        continue;
      }
      Z3_func_decl s2 = sorts[j];
      Z3_symbol symbol2 = Z3_get_decl_name(ctx, s2);
      std::string name2 = Z3_get_symbol_string(ctx, symbol2);
      if (rtcSubsorts[name2].count(name1)) {
        maxLeq = false;
        break;
      }
    }
    for (int j = 0; j < sorts.size(); j++) {
      if (i == j) {
        continue;
      }
      Z3_func_decl s2 = sorts[j];
      Z3_symbol symbol2 = Z3_get_decl_name(ctx, s2);
      std::string name2 = Z3_get_symbol_string(ctx, symbol2);
      if (rtcSyntacticSubsorts[name2].count(name1)) {
        maxLeqSyntax = false;
        break;
      }
    }
    if (maxLeq) {
      maxSortsLeq[i] = true;
    }
    if (maxLeqSyntax) {
      maxSortsLeqSyntax[i] = true;
    }
  }

  propagate->init(sorts, variables, params, subsortsZ3, syntacticSubsortsZ3,
                  minSortsLeq, minSortsLeqSyntax, maxSortsLeq,
                  maxSortsLeqSyntax, idToIdx, leqSort, leqSortSyntax);
  /*
    for (Z3_func_decl param : params) {
      Z3_ast app = Z3_mk_app(ctx, param, 0, nullptr);
      Z3_ast eq = Z3_mk_eq(ctx, app, klabel);
      Z3_ast _not = Z3_mk_not(ctx, eq);
      Z3_solver_assert(ctx, solver, _not);
    }
  */
  std::vector<Z3_symbol> smtSortNames;
  smtSortNames.push_back(sortSymbol);
  std::vector<Z3_sort> smtSorts;
  smtSorts.push_back(sortSort);
  Z3_ast_vector constraints =
      Z3_parse_smtlib2_file(ctx, argv[5], 1, &smtSortNames[0], &smtSorts[0],
                            smtDecls.size(), &smtDeclNames[0], &smtDecls[0]);
  Z3_ast_vector_inc_ref(ctx, constraints);
  for (unsigned i = 0; i < Z3_ast_vector_size(ctx, constraints); i++) {
    Z3_ast constraint = Z3_ast_vector_get(ctx, constraints, i);
    Z3_solver_assert(ctx, solver, constraint);
  }
  // constraint = Z3_substitute_funs(ctx, constraint, 1, &leqSort,
  // &leqSortExp);
  // Z3_solver_assert(ctx, solver, constraint);

  Z3_ast_vector assertions = Z3_solver_get_assertions(ctx, solver);
  Z3_ast_vector_inc_ref(ctx, assertions);
  propagate->setAssertions(assertions);

  Z3_lbool result = Z3_solver_check(ctx, solver);

  while (result == Z3_L_TRUE) {
    std::cout << "sat" << std::endl;
    Z3_model model = Z3_solver_get_model(ctx, solver);
    Z3_model_inc_ref(ctx, model);

    std::vector<Z3_ast> distinct;
    for (Z3_func_decl variable : variables) {
      Z3_ast value = Z3_model_get_const_interp(ctx, model, variable);
      Z3_symbol name = Z3_get_decl_name(ctx, variable);
      std::string s = Z3_get_symbol_string(ctx, name);
      std::cout << "((|" << s << "| " << Z3_ast_to_string(ctx, value) << "))"
                << std::endl;
      Z3_ast args[2];
      args[0] = Z3_mk_app(ctx, variable, 0, nullptr);
      args[1] = value;
      distinct.push_back(Z3_mk_not(ctx, Z3_mk_eq(ctx, args[0], args[1])));
    }
    for (Z3_func_decl variable : params) {
      Z3_ast value = Z3_model_get_const_interp(ctx, model, variable);
      Z3_symbol name = Z3_get_decl_name(ctx, variable);
      std::string s = Z3_get_symbol_string(ctx, name);
      std::cout << "((|" << s << "| " << Z3_ast_to_string(ctx, value) << "))"
                << std::endl;
    }

    Z3_solver_assert(ctx, solver, Z3_mk_or(ctx, distinct.size(), &distinct[0]));
    propagate->reset();
    break;

    result = Z3_solver_check(ctx, solver);
  }
  std::cout << "unsat" << std::endl;

  return 0;
}
