#include<cassert>
#include<map>
#include<string>
#include<iostream>

template<class T>
class Ref {
	struct Body {
		unsigned int nref;
		T body;
		Body() = delete;
		Body(T const& body) : nref(0), body(body) {}
	};
	Body* const ptr;
	Ref() = delete;
public:
	Ref(T const& body) : ptr(new Body(body)) {}
	Ref(Ref const& org) : ptr(org.ptr) {
		ptr->nref++;
	}
	~Ref() {
		if( ptr->nref == 0 ) {
			delete ptr;
		} else {
			ptr->nref--;
		}
	}
	T& operator*() const {
		return ptr->body;
	}
	T* operator->() const {
		return &ptr->body;
	}
};

class Term;

typedef std::map<std::string const, Term const> Subst;

class Term {
	struct App;
	struct Abs;
	enum { SYM, APP, ABS } type;
	union Union {
		char const* const sym;
		Ref<App const> const app;
		Ref<Abs const> const abs;
		Union(char const* sym) : sym(sym) {}
		Union(Ref<App const> const& app) : app(app) {}
		Union(Ref<Abs const> const& abs) : abs(abs) {}
		~Union() {}
	} un;
	Union copy_union() const;
	Term() = delete; // uninitialized construct is not allowed
	Term* operator&() = delete; // making pointer is not allowed
	Term(Term const& fun, Term const& arg); // application
	Term(char const* var, Term const& body); // abstraction
public:
	Term(char const* sym) : type(SYM), un(sym) {} // symbol
	Term(Term const& t) : type(t.type), un(t.copy_union()) {}
	~Term();
	/**
	 * @brief application
	 */
	Term operator()(Term const& arg) const {
		return Term(*this,arg);
	}
	/**
	 * @brief abstraction
	 */
	friend Term operator/(char const* var, Term const& body) {
		return Term(var,body);
	}
	char const* sym() const {
		assert( type == SYM );
		return un.sym;
	}
	Term const& fun() const;
	Term const& arg() const;
	char const* var() const;
	Term const& body() const;
	Term subst(Subst& map) const;
	friend std::ostream& operator<<(std::ostream& os, Term const& t);
};

Term::Union Term::copy_union() const {
	switch(type) {
	case SYM: return Union(un.sym);
	case APP: return Union(un.app);
	case ABS: return Union(un.abs);
	}
}

struct Term::App {
	Term const fun;
	Term const arg;
};

struct Term::Abs {
	char const* const var;
	Term const body;
};

Term::Term(Term const& fun, Term const& arg) : type(APP), un(Ref<App const>(App{fun,arg})) {}

Term::Term(char const* var, Term const& body) : type(ABS), un(Ref<Abs const>(Abs{var,body})) {}

Term::~Term() {
	switch(type) {
	case APP: un.app.~Ref(); break;
	case ABS: un.abs.~Ref(); break;
	case SYM: break;
	}
}

Term const& Term::fun() const {
	assert( type == APP );
	return un.app->fun;
}
Term const& Term::arg() const {
	assert( type == APP );
	return un.app->arg;
}
char const* Term::var() const {
	assert( type == ABS );
	return un.abs->var;
}
Term const& Term::body() const {
	assert( type == ABS );
	return un.abs->body;
}

Term Term::subst(Subst& map) const {
	switch(type) {
		case SYM: {
			auto it = map.find(sym());
			if( it == map.end() ) {
				return *this;
			}
			return it->second;
		}
		case APP:
			return fun().subst(map)(arg().subst(map));
		case ABS: {
			char const* x = var();
			auto it = map.find(x);
			if( it == map.end() ) {
				return x/body().subst(map);
			}
			auto pair = *it;
			map.erase(it);// forget this assignment
			Term const& ret = x/body().subst(map);
			map.insert(pair); // recall the assignment
			return ret;
		}
	}
}

std::ostream& operator<<(std::ostream& os, Term const& t) {
	switch(t.type) {
	case Term::SYM:
		return os << t.sym();
	case Term::APP:
		return os << '(' << t.fun() << ' ' << t.arg() << ')';
	case Term::ABS:
		return os << t.var() << ". " << t.body();
	}
};

int main() {
	Term t = Term("f")(Term("g")(Term("f")(Term("x"))(Term("x"))));
	Term v = Term("h")(Term("a"));
	std::cout << t << std::endl;
	std::cout << v << std::endl;
	Subst map = {{"x",v}};
	std::cout << t.subst(map) << std::endl;
	Term u = "y" / Term("f")(Term("x"))("x" / Term("x")(Term("y")));
	std::cout << u << std::endl;
	std::cout << u.subst(map) << std::endl;

}
