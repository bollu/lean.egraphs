#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <initializer_list>
#include <assert.h>
#include <queue>

const char* __asan_default_options() { return "detect_leaks=0"; }

using namespace std;

using Symbol = int;
struct Eclass; // equiv class. of terms. 
struct Term; // (head symbol, +, -, plus arguments which )are equiv. classes)

struct Term {
  Symbol head;
  vector<Eclass *> args;
  bool operator < (const Term &other) const {
    if (head < other.head) { return true; }
    if (head > other.head) { return false; }
    assert (head == other.head);
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
    printf("[%4d", head);
    for(int i = 0; i < args.size(); ++i) {
      printf(", %4p", args[i]);
    }
    printf("]");
  }
};






// E1 = [1] | parent: ((+ [E1] [E2]), E3)
// E2 = [2]
// E-1 = [-1]
// E4 = [4]
// E3 = [ (+ [E1] [E2]), (+ [E-1] [E4])]
// equivalence class.
struct Eclass {
  // terms that point to this e-class. memory owned by egraph.
  vector<pair<Term, Eclass*>> parentTerms;
  // 1) data for union-find.[3]
  Eclass *ufparent; // parent in the union-find ttee  4
  int ufSubtreeSize; // size of the subtree

  static Eclass *singleton() {
    Eclass *cls = new Eclass;
    cls->ufparent = cls;
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
private:
  Eclass() {};
};



struct Egraph {
  // the ONLY global data tracked is
  // *canonicalized terms* to the equivalence classes they belong to.  
  map<Term, Eclass *> term2class;

  Eclass *canonicalizeClass(Eclass *cls) const {
    assert(cls);
    if (cls->ufparent == cls) { return cls; }
    cls->ufparent = canonicalizeClass(cls->ufparent);
    return cls->ufparent;
  }

  Term canonicalizeTerm (Term tm) const {
    for(int i = 0; i < tm.args.size(); ++i) {
      tm.args[i] = canonicalizeClass(tm.args[i]);
      assert(tm.args[i] != nullptr);
    }
    return tm;
  }

  Eclass *getTermClass (Term tm) const {
    tm = canonicalizeTerm(tm);
    auto it = term2class.find(tm);
    if (it == term2class.end()) {
      assert(false && "expected to have term in e-graph.");
    }
    return it->second;
  }

  Eclass* findOrAddTerm (Term tm) {
    tm = canonicalizeTerm(tm);
    Eclass *cls = nullptr;
    auto it = term2class.find(tm);
    if (it == term2class.end()) {
        cls = Eclass::singleton();
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

    for (std::pair<Term, Eclass*> tm : child->parentTerms) {
      parent->parentTerms.push_back(tm);
    }

    rebuild(parent);
    return parent;
  };

  void rebuild(Eclass *cls) {
    printf("rebuilding eclass: "); cls->print(); printf("\n");
    // invariant: the Eterm, Eclass must be the latest Eclass.
    vector<std::pair<Term, Eclass *>> canonParents;
    for(std::pair<Term, Eclass *> tmcls : cls->parentTerms) {
      // TODO: why can't this give us a radically different term, which
      // DOES NOT in fact exist in our database of terms?
      tmcls.first = canonicalizeTerm(tmcls.first);
      Eclass *newclass = getTermClass(tmcls.first);
      assert(newclass != nullptr); // TODO: why MUST this exist?
      if (newclass == tmcls.second) { continue; }
      // canonical version of term has changed, time to unite!
      tmcls.second = unite(newclass, tmcls.second);
      term2class[tmcls.first] = tmcls.second;
      canonParents.push_back(tmcls);
    }
    cls->parentTerms = canonParents;

  }
};

// A completely constant class used to build terms.
struct TermBuilder {
  const Symbol sym;
  const vector<TermBuilder *> args;

  TermBuilder(Symbol sym, initializer_list<TermBuilder *> args) :
    sym(sym), args(args) {}

  static TermBuilder* mk(const Symbol sym) {
    return new TermBuilder(sym, {});
  }

  static TermBuilder* mk(const Symbol sym, TermBuilder *arg1) {
    return new TermBuilder(sym, {arg1});
  }

  static TermBuilder* mk(const Symbol sym,
			 TermBuilder *arg1,
			 TermBuilder *arg2) {
    return new TermBuilder(sym, {arg1, arg2});
  }


  template<typename ...Args>
  static TermBuilder* mk(const Symbol sym, Args... args) {
    return new TermBuilder(sym, args...);
  }

  Eclass* addToEgraph(Egraph &e) const {
    Term tm;
    tm.head = sym;
    for(int i = 0; i < this->args.size(); ++i) {
      tm.args.push_back(this->args[i]->addToEgraph(e));
    }
    return e.findOrAddTerm(tm);
  }
};

static const int CST = 0;
static const int ADD = 100;
static const int NEG = 200;
void test() {
  Egraph g;
  cout << "adding same constants\n";
  Eclass *cls1 = TermBuilder::mk(CST + 10)->addToEgraph(g);
  Eclass *cls2 = TermBuilder::mk(CST + 10)->addToEgraph(g);
    assert(cls1 == cls2);
}

void test2() {
  Egraph g;
  cout << "adding different constants\n";
  Eclass *cls1 = TermBuilder::mk(CST + 10)->addToEgraph(g);
  Eclass *cls2 = TermBuilder::mk(CST + 20)->addToEgraph(g);
  assert(cls1 != cls2);
}


void test3() {
  Egraph g;
  cout << "adding different constants, then uniting them\n";
  Eclass *cls1 = TermBuilder::mk(CST + 10)->addToEgraph(g);
  Eclass *cls2 = TermBuilder::mk(CST + 20)->addToEgraph(g);
  assert(cls1 != cls2);
  g.unite(cls1, cls2);
  cls1 = g.canonicalizeClass(cls1);
  cls2 = g.canonicalizeClass(cls2);
  assert(cls1 == cls2);
}


void test4() {
  Egraph g;
  cout << "adding three constants, then uniting unrelated ones \n";
  Eclass *cls1 = TermBuilder::mk(CST + 10)->addToEgraph(g);
  Eclass *cls2 = TermBuilder::mk(CST + 20)->addToEgraph(g);
  Eclass *cls3 = TermBuilder::mk(CST + 30)->addToEgraph(g);
  assert(cls1 != cls2);
  assert(cls2 != cls3);
  assert(cls1 != cls3);
  g.unite(cls1, cls3);
  cls1 = g.canonicalizeClass(cls1);
  cls2 = g.canonicalizeClass(cls2);
  cls3 = g.canonicalizeClass(cls3);
  assert(cls1 == cls3);
  assert(cls1 != cls2);
}


void test5() {
  Egraph g;
  cout << "adding subtrees, then uniting children\n";


  Eclass *cls1 =
    TermBuilder::mk(NEG, TermBuilder::mk(CST + 10))->addToEgraph(g);
  Eclass *cls2 =
    TermBuilder::mk(NEG, TermBuilder::mk(CST + 20))->addToEgraph(g);
  Eclass *cls3 =
    TermBuilder::mk(NEG, TermBuilder::mk(CST + 30))->addToEgraph(g);

  assert(cls1 != cls2);
  assert(cls1 != cls3);
  assert(cls2 != cls3);

  Eclass *cst1 = TermBuilder::mk(CST + 10)->addToEgraph(g);
  Eclass *cst2 = TermBuilder::mk(CST + 20)->addToEgraph(g);
  Eclass *cst3 = TermBuilder::mk(CST + 30)->addToEgraph(g);
  assert(cst1 != cst2);
  assert(cst2 != cst3);
  assert(cst1 != cst3);

  g.unite(cst1, cst2);

  cst1 = g.canonicalizeClass(cst1);
  cst2 = g.canonicalizeClass(cst2);
  cst3 = g.canonicalizeClass(cst3);
  assert(cst1 == cst2);
  assert(cst1 != cst3);

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
    TermBuilder::mk(NEG, TermBuilder::mk(CST + 10))->addToEgraph(g);
  Eclass *cls2 = // - 20
    TermBuilder::mk(NEG, TermBuilder::mk(CST + 20))->addToEgraph(g);
  Eclass *cls3 =
    TermBuilder::mk(NEG, TermBuilder::mk(CST + 30))->addToEgraph(g);

  assert(cls1 != cls2);
  assert(cls1 != cls3);
  assert(cls2 != cls3);

  Eclass *cst1 = TermBuilder::mk(CST + 10)->addToEgraph(g);
  Eclass *cst2 = TermBuilder::mk(CST + 20)->addToEgraph(g);
  Eclass *cst3 = TermBuilder::mk(CST + 30)->addToEgraph(g);
  assert(cst1 != cst2);
  assert(cst2 != cst3);
  assert(cst1 != cst3);

  g.unite(cst1, cst2); // 10 = 20 
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
  Eclass *f = TermBuilder::mk(CST + 10)->addToEgraph(g);
  vector<Eclass *> fs;
  fs.push_back(TermBuilder::mk(CST + 0)->addToEgraph(g)); // id
  fs.push_back(f); // f

  // add upto f^10.
  for(int i = 2; i <= 20; ++i) {
    Term tm;
    tm.head = CST + 10;
    tm.args = { fs[i-1] } ;
    fs.push_back(g.findOrAddTerm(tm));
  }

  g.unite(fs[2], fs[6]);

  for(Eclass *& cls : fs) {
    cls = g.canonicalizeClass(cls);
  }
  assert(fs[3] == fs[7]);
  assert(fs[3] != fs[8]);
  assert(fs[4] == fs[8]);
  assert(fs[4] == fs[12]);
  assert(fs[4] != fs[7]);
}
int main() {
  test();
  test2();
  test3();
  test4();
  test5();
  test6();
  test7();
}
