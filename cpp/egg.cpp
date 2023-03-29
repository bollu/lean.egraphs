#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <initializer_list>
#include "assert.h"
#include <queue>
#include <functional>
#include <optional>
#include <set>

const char* __asan_default_options() { return "detect_leaks=0"; }

using namespace std;

using Symbol = int;
struct Eclass; // equiv class. of terms.
struct HashConsTerm; // (sym symbol, +, -, plus arguments which )are equiv. classes)
struct Pattern;
struct Term;

using EclassPtr = int;

struct HashConsTerm {
  Symbol sym;
  vector<Eclass *> args;

  bool operator == (const HashConsTerm &other) const {
    if (sym != other.sym) { return false; }
    if (args.size() != other.args.size()) { return false; }
    for(int i = 0; i < args.size(); ++i) {
      if (args[i] != other.args[i]) { return false; }
    }
    return true;
  }

  bool operator < (const HashConsTerm &other) const {
    if (sym < other.sym) { return true; }
    if (sym > other.sym) { return false; }
    assert (sym == other.sym);
    if (args.size() < other.args.size()) { return true; }
    if (args.size() > other.args.size()) { return false; }
    assert(args.size() == other.args.size());
    for(int i = 0; i < args.size(); ++i) {
      if (args[i] < other.args[i]) { return true; }
      if (args[i] > other.args[i]) { return false; }
    }
    return false; // not less than, strictly equal.
  }

  void print() const {
    printf("[%4d", sym);
    for(int i = 0; i < args.size(); ++i) {
      printf(", %4p", args[i]);
    }
    printf("]");
  }
};


// === E-classes ===




// E1 = [1] | parent: ((+ [E1] [E2]), E3)
// E2 = [2]
// E-1 = [-1]
// E4 = [4]
// E3 = [ (+ [E1] [E2]), (+ [E-1] [E4])]
// equivalence class.
struct Eclass {
  // terms that point to this e-class. memory owned by egraph.
  vector<pair<HashConsTerm, Eclass*>> parentTerms;
  vector<HashConsTerm> members;
  // 1) data for union-find.[3]
  Eclass *ufparent; // parent in the union-find ttee  4
  int ufSubtreeSize; // size of the subtree
  static Eclass *singleton(HashConsTerm tm) {
    Eclass *cls = new Eclass;
    cls->ufparent = cls;
    cls->members = {tm};
    cls->ufSubtreeSize = 1;
    return cls;
  }

  void print() const {
    printf("{^%5p | ", ufparent);
    if (!parentTerms.size()) {
      printf(" }");
      return;
    }
    printf(" | parentTerms ");
    for(auto tm_and_class : parentTerms) {
      printf(", ");
      printf("%5x -> ", tm_and_class.second);
      tm_and_class.first.print();
    }
    printf(" }");
  }

  void assertInvariants(Egraph *g);
private:
  Eclass() {};
};




struct Egraph {
  // the ONLY global data tracked is
  // *canonicalized terms* to the equivalence classes they belong to.
  map<HashConsTerm, Eclass *> term2class;

  void assertTerm2ClassInvariant() {
    for(auto it : term2class) {
      // key should be canonical.
      HashConsTerm tm2 = canonicalizeHashConsTerm_(it.first);
      assert(tm2 == it.first);

      it.second.assertInvariants(&g);
    }
  }

  void assertInvariants() {
    assertTerm2ClassInvariant();
  }

  Eclass *canonicalizeClass(Eclass *cls) const {
    assert(cls);
    if (cls->ufparent == cls) { return cls; }
    cls->ufparent = canonicalizeClass(cls->ufparent);
    return cls->ufparent;
  }

  HashConsTerm canonicalizeHashConsTerm_(HashConsTerm tm) {
    for (int i = 0; i < tm.args.size(); ++i) {
      tm.args[i] = canonicalizeClass(tm.args[i]);
      assert(tm.args[i] != nullptr);
    }
    return tm;
  }


  
  Eclass* findOrAddHashConsTerm (HashConsTerm tm) {
    // canonicalize tm
    tm = canonicalizeHashConsTerm_(tm);
    
    // find
    Eclass *cls = nullptr;
    auto it = term2class.find(tm);
    if (it == term2class.end()) {
        // add
        cls = Eclass::singleton(tm);
      term2class[tm] = cls;
    } else {
      cls = it->second;
    }

    assert(cls);
    for(Eclass *argcls : tm.args) {
      argcls->parentTerms.push_back({tm, cls});
    }
    printf("adding term "); tm.print(); printf("\n");
    return cls;
  };


  // Ea, Eb
  // canonicalize(NEG(Eb)) = NEG(Eb)

  // NEG (Ea)
  // NEG (Eb)
  // union(Ea, Eb)
  // Ea <- Eb
  // canonicalize(NEG(Eb)) = NEG(Ea)
  Eclass *unite(Eclass *a, Eclass *b) {
    assert(a); assert(b);
    a = canonicalizeClass(a);
    b = canonicalizeClass(b);

    printf("uniting: ");
    printf("\n  - "); a->print();
    printf("\n  - "); b->print(); printf("\n");
    assert(a);
    assert(b);


    if (a == b) { return a; }
    // attach root of smaller subtree
    // to root of larger subtree.
    // This makes sure that if we have a long chain
    // (l1 <- l2 <- l3) and another chain (r1), we
    // attach it as: (r1 -> l1 <- l2 <- l3), keeping depth
    // the same, instead of (l1 <- l2 <- l3 <- r1)nn
    Eclass *child = nullptr,  *parent = nullptr;
    if (a->ufSubtreeSize < b->ufSubtreeSize) {
      parent = b; child = a;
    } else {
      parent = a; child = b;
    }
    assert(parent); assert(child);

    child->ufparent = parent;
    parent->ufSubtreeSize += child->ufSubtreeSize;

    for (HashConsTerm tm : child->members) {
      parent->members.push_back(tm);
    }

    for (std::pair<HashConsTerm, Eclass*> tm : child->parentTerms) {
      parent->parentTerms.push_back(tm);
    }

    rebuild(parent);
    return parent;
  };


  void rebuild(Eclass *cls) {
    printf("rebuilding eclass: "); cls->print(); printf("\n");
    // invariant: the Eterm, Eclass must be the latest Eclass.
    vector<std::pair<HashConsTerm, Eclass *>> canonParents;
    // keep a copy to prevent iterator invalidation!
    vector<std::pair<HashConsTerm, Eclass *>> parentTerms = cls->parentTerms;
    printf("cls size: %d\n", cls->parentTerms.size());
    for(std::pair<HashConsTerm, Eclass *> tmcls : parentTerms) {
      Eclass *newclass = findOrAddHashConsTerm(tmcls.first);
      assert(newclass != nullptr); // TODO: why MUST this exist?
      if (newclass == tmcls.second) { continue; } // already canonical.
      // not canonical, unite with new version.
      tmcls.second = unite(newclass, tmcls.second);
      // update table. TODO: why is table up to date at this point?
      term2class.erase(tmcls.first);
      tmcls.first = canonicalizeHashConsTerm_(tmcls.first);
      term2class[tmcls.first] = tmcls.second;
      canonParents.push_back(tmcls);
    }
    // prevent iterator invalidation.
    cls->parentTerms = canonParents;

  }
};


void Eclass::assertInvariants(Egraph *g) {
 

}

// === terms ===


// A completely constant class used to build hash cons terms.
struct Term {
  const Symbol sym;
  const vector<Term *> args;

  Term(Symbol sym, initializer_list<Term *> args) :
    sym(sym), args(args) {}

  static Term* mk(const Symbol sym) {
    return new Term(sym, {});
  }

  static Term* mk(const Symbol sym, Term *arg1) {
    return new Term(sym, {arg1});
  }

  static Term* mk(const Symbol sym,
			 Term *arg1,
			 Term *arg2) {
    return new Term(sym, {arg1, arg2});
  }


  template<typename ...Args>
  static Term* mk(const Symbol sym, Args... args) {
    return new Term(sym, args...);
  }

  Eclass* addToEgraph(Egraph &e) const {
    HashConsTerm tm;
    tm.sym = sym;
    for(int i = 0; i < this->args.size(); ++i) {
      tm.args.push_back(this->args[i]->addToEgraph(e));
    }
    return e.findOrAddHashConsTerm(tm);
  }
};

// === patterns over terms ===

using VarId = int;

using PatternCtx = std::map<VarId, HashConsTerm>;


struct Pattern {
  Egraph *graph;
  using Callback = std::function<void(PatternCtx)>;
  Pattern (Egraph *graph) : graph(graph) {};
  virtual optional<HashConsTerm> subst(PatternCtx pctx) = 0;
  virtual void unify(HashConsTerm tm, PatternCtx pctx, Pattern::Callback cb) = 0;
  virtual void unify(Eclass *ecls, PatternCtx pctx, Pattern::Callback cb) {
    for(HashConsTerm tm : ecls->members) {
      unify(tm, pctx, cb);
    }
  }

};

struct PatternVar : public Pattern {
  VarId id;
  PatternVar(Egraph *graph, VarId id) :
    Pattern(graph), id(id) {}

  optional<HashConsTerm> subst(PatternCtx pctx) {
    auto it = pctx.find(this->id);
    if (it == pctx.end()) { return {}; }
    return {it->second};
  }

  virtual void unify(HashConsTerm tm, PatternCtx pctx, Pattern::Callback cb) {
    auto it = pctx.find(id);
    if (it == pctx.end()) {
      pctx[id] = tm;
      cb(pctx);
     } else if (it->second == tm) {
      cb(pctx);
     }
  }
};

struct PatternTerm : public Pattern {
  Symbol sym;
  vector<Pattern *> args;

  PatternTerm(Egraph *graph,
    Symbol sym, vector<Pattern *> args) :
    Pattern(graph), sym(sym), args(args) {};

  static PatternTerm *mk(Egraph *graph, Symbol sym, Pattern *arg1) {
      vector<Pattern *> args = {arg1};
      return new PatternTerm(graph, sym, args);
  }

  static PatternTerm *mk(Egraph *graph, Symbol sym, Pattern *arg1, Pattern *arg2) {
      vector<Pattern *> args = {arg1, arg2};
      return new PatternTerm(graph, sym, args);
  }

  optional<HashConsTerm> subst(PatternCtx pctx) {
    HashConsTerm tm;
    tm.sym = sym;

    for(Pattern * p : args) {
      optional<HashConsTerm> otm = p->subst(pctx);
      if(!otm) { return {}; }
      tm.args.push_back(graph->findOrAddHashConsTerm(*otm));
    }
    return tm;
  }

  virtual void unify(HashConsTerm tm, PatternCtx pctx, Pattern::Callback cb) {
    if (tm.sym != sym) { return; }
    if (tm.args.size() != args.size()) { return; }

    vector<PatternCtx> states;
    states.push_back(pctx);

    for(int i = 0; i < args.size(); ++i) {
      vector<PatternCtx> newstates;
      for(PatternCtx pctx : states) {
        for(HashConsTerm argtm : tm.args[i]->members) {
           args[i]->unify(argtm, pctx, [&](PatternCtx newpctx) {
              newstates.push_back(newpctx);
           });
        }
      }
      states = newstates;
    }

    for(PatternCtx pctx : states) { cb(pctx); }
  }
};

void patternGetFreeVars(Pattern *p, std::set<Pattern *> &out) {
    assert(p);
    if (auto pt = dynamic_cast<PatternTerm *>(p)) {
        for(Pattern *p : pt->args) {
            patternGetFreeVars(pt, out);
        }
    } else {
        auto pv = dynamic_cast<PatternVar *>(p);
        out.insert(pv);
    }
};

std::set<Pattern *> patternGetFreeVars(Pattern *p) {
    std::set<Pattern *> out;
    patternGetFreeVars(p, out);
    return out;
}

struct Rewrite {
    Pattern *lhs;
    Pattern *rhs;

    Rewrite(Pattern *lhs, Pattern *rhs) : lhs(lhs), rhs(rhs) {
        // TODO: check that free vars(lhs) subset free vars(rhs)
    }

    // try to apply the rewrite, converting the lhs into the rhs.
    optional<HashConsTerm> apply(HashConsTerm ht) {
        optional<PatternCtx> opctx;
        this->lhs->unify(ht, {}, [&](PatternCtx pctx) {
            opctx = pctx;
        });
        if (opctx) { return rhs->subst(*opctx); }
        return {};
    }
};

static const int CST = 0;
static const int ADD = 100;
static const int NEG = 200;
static const int X = -42; // variable
void test() {
  Egraph g;
  cout << "adding same constants\n";
  Eclass *cls1 = Term::mk(CST + 10)->addToEgraph(g);
  g.assertInvariants();
  Eclass *cls2 = Term::mk(CST + 10)->addToEgraph(g);
  g.assertInvariants();
  assert(cls1 == cls2);
}

void test2() {
  Egraph g;
  cout << "adding different constants\n";
  Eclass *cls1 = Term::mk(CST + 10)->addToEgraph(g);
  g.assertInvariants();
  Eclass *cls2 = Term::mk(CST + 20)->addToEgraph(g);
  assert(cls1 != cls2);
}


void test3() {
  Egraph g;
  cout << "adding different constants, then uniting them\n";
  Eclass *cls1 = Term::mk(CST + 10)->addToEgraph(g);
  g.assertInvariants();
  Eclass *cls2 = Term::mk(CST + 20)->addToEgraph(g);
  g.assertInvariants();
  assert(cls1 != cls2);
  g.unite(cls1, cls2);
  cls1 = g.canonicalizeClass(cls1);
  g.assertInvariants();
  cls2 = g.canonicalizeClass(cls2);
  assert(cls1 == cls2);
}


void test4() {
  Egraph g;
  cout << "adding three constants, then uniting unrelated ones \n";
  Eclass *cls1 = Term::mk(CST + 10)->addToEgraph(g);
  g.assertInvariants();
  Eclass *cls2 = Term::mk(CST + 20)->addToEgraph(g);
  g.assertInvariants();
  Eclass *cls3 = Term::mk(CST + 30)->addToEgraph(g);
  g.assertInvariants();
  assert(cls1 != cls2);
  assert(cls2 != cls3);
  assert(cls1 != cls3);
  g.unite(cls1, cls3);
  g.assertInvariants();
  cls1 = g.canonicalizeClass(cls1);
  g.assertInvariants();
  cls2 = g.canonicalizeClass(cls2);
  g.assertInvariants();
  cls3 = g.canonicalizeClass(cls3);
  g.assertInvariants();
  assert(cls1 == cls3);
  assert(cls1 != cls2);
}


void test5() {
  Egraph g;
  cout << "adding subtrees, then uniting children\n";


  Eclass *cls1 =
    Term::mk(NEG, Term::mk(CST + 10))->addToEgraph(g);
  Eclass *cls2 =
    Term::mk(NEG, Term::mk(CST + 20))->addToEgraph(g);
  Eclass *cls3 =
    Term::mk(NEG, Term::mk(CST + 30))->addToEgraph(g);

  assert(cls1 != cls2);
  assert(cls1 != cls3);
  assert(cls2 != cls3);

  Eclass *cst1 = Term::mk(CST + 10)->addToEgraph(g);
  Eclass *cst2 = Term::mk(CST + 20)->addToEgraph(g);
  Eclass *cst3 = Term::mk(CST + 30)->addToEgraph(g);
  assert(cst1 != cst2);
  assert(cst2 != cst3);
  assert(cst1 != cst3);

  g.unite(cst1, cst2);
  g.assertInvariants();
  
  cst1 = g.canonicalizeClass(cst1);
  cst2 = g.canonicalizeClass(cst2);
  cst3 = g.canonicalizeClass(cst3);
  assert(cst1 == cst2);
  assert(cst1 != cst3);
  g.assertInvariants();

  cls1 = g.canonicalizeClass(cls1);
  cls2 = g.canonicalizeClass(cls2);
  cls3 = g.canonicalizeClass(cls3);
  assert(cls1 == cls2);
  assert(cls1 != cls3);


}

void test6() {
  Egraph g;
  cout << "adding subtrees, then uniting all children\n" ;


  Eclass *cls1 = // - 10
    Term::mk(NEG, Term::mk(CST + 10))->addToEgraph(g);
  Eclass *cls2 = // - 20
    Term::mk(NEG, Term::mk(CST + 20))->addToEgraph(g);
  Eclass *cls3 =
    Term::mk(NEG, Term::mk(CST + 30))->addToEgraph(g);

  assert(cls1 != cls2);
  assert(cls1 != cls3);
  assert(cls2 != cls3);

  Eclass *cst1 = Term::mk(CST + 10)->addToEgraph(g);
  Eclass *cst2 = Term::mk(CST + 20)->addToEgraph(g);
  Eclass *cst3 = Term::mk(CST + 30)->addToEgraph(g);
  assert(cst1 != cst2);
  assert(cst2 != cst3);
  assert(cst1 != cst3);

  g.unite(cst1, cst2); // 10 = 20
  g.assertInvariants();
  g.unite(cst1, cst3);

  cst1 = g.canonicalizeClass(cst1);
  cst2 = g.canonicalizeClass(cst2);
  cst3 = g.canonicalizeClass(cst3);
  assert(cst1 == cst2);
  assert(cst1 == cst3);

  cls1 = g.canonicalizeClass(cls1);
  cls2 = g.canonicalizeClass(cls2);
  cls3 = g.canonicalizeClass(cls3);
  assert(cls1 == cls2); // - 10 == - 20
  assert(cls1 == cls3);
}


// f^2 = f^6
// implies f^3 = f7
void test7() {
  Egraph g;
  Eclass *f = Term::mk(CST + 10)->addToEgraph(g);
  vector<Eclass *> fs;
  fs.push_back(Term::mk(CST + 0)->addToEgraph(g)); // id
  g.assertInvariants();    
  fs.push_back(f); // f

  // add upto f^10.
  for(int i = 2; i <= 20; ++i) {
    HashConsTerm tm;
    tm.sym = CST + 10;
    tm.args = { fs[i-1] } ;
    fs.push_back(g.findOrAddHashConsTerm(tm));
    g.assertInvariants();
  }

  g.unite(fs[2], fs[6]);
  g.assertInvariants();

  for(Eclass *& cls : fs) {
    cls = g.canonicalizeClass(cls);
  }
  assert(fs[3] == fs[7]);
  assert(fs[3] != fs[8]);
  assert(fs[4] == fs[8]);
  assert(fs[4] == fs[12]);
  assert(fs[4] != fs[7]);
}

// This tests that new equivalence classes are created correctly.
void test8() {
  Egraph g;
  cout << "adding subtrees, then uniting all children\n" ;


  Eclass *cls1 = // - 10
    Term::mk(NEG, Term::mk(CST + 10))->addToEgraph(g);

  Eclass *cst1 = Term::mk(CST + 10)->addToEgraph(g);
  Eclass *cst2 = Term::mk(CST + 20)->addToEgraph(g);
  assert(cst1 != cst2);

  g.unite(cst1, cst2); // 10 = 20
  // note that this triggers the creation of a (- 20) in some sense.


  cls1 = g.canonicalizeClass(cls1);
  Eclass *cls2 = // - 20
    Term::mk(NEG, Term::mk(CST + 20))->addToEgraph(g);

  assert(cls1 == cls2); // - 10 == - 20

}

void test9() {
  // test 8 with unite in opposite order.
  Egraph g;
  cout << "adding subtrees, then uniting all children\n" ;


  Eclass *cls1 = // - 10
    Term::mk(NEG, Term::mk(CST + 10))->addToEgraph(g);

  Eclass *cst1 = Term::mk(CST + 10)->addToEgraph(g);
  Eclass *cst2 = Term::mk(CST + 20)->addToEgraph(g);
  assert(cst1 != cst2);

  g.unite(cst2, cst1); // 20 = 10
  // note that this triggers the creation of a (- 20) in some sense.


  cls1 = g.canonicalizeClass(cls1);
  Eclass *cls2 = // - 20
    Term::mk(NEG, Term::mk(CST + 20))->addToEgraph(g);

  assert(cls1 == cls2); // - 10 == - 20
}


void test10() {
// extract out all values from an e-class
  Egraph g;
  Eclass *cls1 = Term::mk(CST + 1)->addToEgraph(g);
  Eclass *cls2 = Term::mk(CST + 2)->addToEgraph(g);
  Eclass *cls3 = Term::mk(CST + 3)->addToEgraph(g);
  Eclass *cls4 = Term::mk(CST + 4)->addToEgraph(g);

  g.unite(cls1, cls2);
  g.unite(cls2, cls3);

  Pattern *p = new PatternVar(&g, X + 1);
  set<HashConsTerm> tms;
  p->unify(cls1, {}, [&](PatternCtx ctx) {
    optional<HashConsTerm> otm = p->subst(ctx);
    if (otm) {
      tms.insert(*otm);
    }
  });

  // check that all terms were extracted.
  assert(tms.size() == 3);
}

void test11() {
  // check that when ({1, 2} + {1, 2}) is in the same eclass, we still
  // pick out only (1 + 1, 2 + 2) if the patern demands it.
  Egraph g;
  auto cst1 = Term::mk(CST + 1);
  auto cst2 = Term::mk(CST + 2);
  Eclass *cls1 = cst1->addToEgraph(g);
  Eclass *cls2 = cst2->addToEgraph(g);
  Eclass *add11 = Term::mk(ADD, cst1, cst1)->addToEgraph(g);
  Eclass *add12 = Term::mk(ADD, cst1, cst2)->addToEgraph(g);
  Eclass *add21 = Term::mk(ADD, cst2, cst1)->addToEgraph(g);
  Eclass *add22 = Term::mk(ADD, cst2, cst1)->addToEgraph(g);

  g.unite(add11, add12);
  g.unite(add12, add21);
  g.unite(add21, add22);

  Pattern *px = new PatternVar(&g, X + 1);
  Pattern *paddxx = PatternTerm::mk(&g, ADD, px, px);

  paddxx->unify(add11, {}, [&](PatternCtx ctx) {
        cerr << "ctx: [";
        for(auto it  : ctx) {
          cerr << it.first << "|->" << it.second.sym << " ";
        }
        cerr << "]\n";
        auto it = ctx.find(X + 1);
        assert(it != ctx.end());
        optional<HashConsTerm> ot = paddxx->subst(ctx);
        assert(ot && "unable to substitute");
        HashConsTerm t = *ot;

        assert(t.sym == ADD);
        assert(t.args.size() == 2);
        assert(t.args[0] == t.args[1]);
  });

}

void test12() {
  //test that unify() actually updates the term table.
  Egraph g;
  auto cst1 = Term::mk(CST + 1);
  auto cst2 = Term::mk(CST + 2);
  Eclass *cls1 = cst1->addToEgraph(g);
  Eclass *cls2 = cst2->addToEgraph(g);
  Eclass *canon = g.unite(cls1, cls2);

  // this should succeed, since table should have cst1 -> canon
  Eclass *cls11 = cst1->addToEgraph(g);
  assert(canon == cls11);

  // this should succeed, since table should have cst2 -> cst1 -> canon
  Eclass *cls22 = cst2->addToEgraph(g);
  assert(canon == cls22);
  
}


int main() {
  test();
  test2();
  test3();
  test4();
  test5();
  test6();
  test7();
  test8();
  test9();
  test10();
  test11();
  test12();
}
