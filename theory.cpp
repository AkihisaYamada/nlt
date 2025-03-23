#include"rewriter.hpp"

using namespace std;

struct Thy::_Body {
	Opt<Thy const> parent;
	std::string name;
	StrMMap<std::pair<Thm,ThmInfo>> thms;
	StrMap<Thy const> thys;
	Map<size_t,std::string> assm_names;
	std::multimap<std::string,Import,std::less<>> imports;
	Mem<Rewriter> rewriter;
	_Body( std::string_view const& name ) : name(name), rewriter(Mem<Rewriter>::make()) {}
	_Body( Thy const& parent, std::string_view const& name ) : parent(parent), name(name), rewriter(parent._ref->rewriter) {
	}
};

Thy::Thy( std::string_view const& name ) : _ref(Ref<_Body>::make(name)) {};

Thy::Thy( Thy const& parent, Ctxt const& ctxt ) :
	Ctxt(ctxt), _ref(Ref<_Body>::make(parent,"")) {}

Thy Thy::branch() const {
	return Thy(Ref<_Body>::make(*this,""), Ctxt::branch());
}
Thy Thy::branch( std::string_view const& name ) {
	auto const& loc = Thy(Ref<_Body>::make(*this,name), Ctxt::branch());
	_ref->thys.emplace(name,loc);
	return loc;
}
Opt<Thy const> Thy::parent() const {
	return _ref->parent;
}
Opt<AThm> Thy::find_thm(
	std::string_view const& name,
	std::function<bool(AThm const&)> const& test,
	bool ancestor,
	bool noprefix
) const {
	return _find_thm(name,_triv_proc,test,ancestor,noprefix,*this);
}
Rewriter const& Thy::rewriter() const& {
	return *_ref->rewriter;
}
Rewriter& Thy::rewriter() & {
	return *_ref->rewriter;
}
AThm Thy::thm(std::string_view const& name) const {
	if( auto opt = find_thm(name) ) {
		return *opt;
	}
	throw TheoremNotFound(name);
}
Opt<std::string> Thy::find_assm_name( size_t rev ) const {
	if( auto x = _ref->assm_names.finds(rev) ) {
		return x->second;
	}
	return {};
}
StrMMap<Import> const& Thy::imports() const {
	return _ref->imports;
}
Import& Thy::import(std::string_view const& name, Thy const& loc) & {
	auto it = _ref->imports.emplace(std::piecewise_construct,
		std::make_tuple(name),
		std::forward_as_tuple(*this,loc)
	);
	return it->second;
};

Thy::Error const Thy::ThyNotFound = Error("\"theory not found\"");

function<Thm(Thm const&)> const Thy::_triv_proc =
	[]( Thm const& thm ) { return thm; };

function<bool(AThm const&)> const Thy::_triv_test =
	[]( AThm const& ) { return true; };

Thm Thy::add_assm(string_view const& name, CTerm const& assm) {
	size_t rev = revision();
	_ref->assm_names.emplace(rev,name);
	return assume(assm);
}

AThm Thy::add_thm(string_view const& name, Thm const& thm, ThmInfo const& info) {
	if( thm.ctxt() != *this ) {
		throw Error("\"add_thm\"")(thm);
	}
	_ref->thms.emplace(name,pair(thm,info));
	return AThm(*this,thm,info);
}

pair<CTerm,Thm> Thy::obtain( string_view const& sym, Thm const& ex, string_view const& spec_name ) {
	size_t rev = revision();
	auto const& ret = Ctxt::obtain(sym,ex);
	add_thm(spec_name,ret.second);
	_ref->assm_names.emplace(rev,spec_name);
	return ret;
}
Opt<AThm> Thy::_find_thm(
	string_view const& name,
	function<Thm(Thm const&)> const& proc,
	function<bool(AThm const&)> const& test,
	bool ancestor,
	bool noprefix,
	Thy const& orig
) const {
	for( auto [it,end] = _ref->thms.equal_range(name); it != end; it++ ) {
		auto const& ret = AThm(orig,proc(it->second.first),it->second.second);
		if( test(ret) ) {// found in the current theory
			return ret;
		}
	}
	if( noprefix ) {
		for( auto const& [pre,imp] : _ref->imports ) {
			if( auto const& ret = imp._find_thm(name,proc,test,noprefix,orig) ) {
				return ret;
			}
		}
	} else {
		auto sep = name.find('.');
		if( sep == 0 ) {// explicit parent
			auto opt = _ref->parent;
			if( !opt ) throw Error("\"parent theory not found\"");
			return opt->_find_thm(name.substr(1),proc,test,ancestor,noprefix,orig);
		}
		if( sep != string::npos ) {// named imports
			if( auto ret = _find_thm(name.substr(0,sep),name.substr(sep+1),proc,test,orig) ) {
				return ret;
			}
		}
		if( auto ret = _find_thm("",name,proc,test,orig) ) {// unnamed import
			return ret;
		}
	}
	if( ancestor )
	if( auto p = _ref->parent ) {
		auto const& proc2 = [&]( Thm const& thm ) {
			return proc(thm.weaken(*this));
		};
		return p->_find_thm(name,proc2,test,ancestor,noprefix,orig);
	}
	return {};
}
Opt<AThm> Thy::_find_thm(
	string_view const& pre,
	string_view const& name,
	function<Thm(Thm const&)> const& proc,
	function<bool(AThm const&)> const& test,
	Thy const& orig
) const {
	// pre as interpretations
	for( auto [it,end] = _ref->imports.equal_range(pre); it != end; it++ ) {
		if( auto opt = it->second._find_thm(name,proc,test,false,orig) ) {
			return opt;
		}
	}
	return {};
}
Opt<AThm> Import::_find_thm(
	string_view const& name,
	function<Thm(Thm const&)> const& proc,
	function<bool(AThm const&)> const& test,
	bool noprefix,
	Thy const& orig
) const {
	if( ready() ) {// only find if the interpretation is ready
		auto const& proc2 = [&]( Thm const& thm ){
			return proc(Intp::subst(thm));
		};
		return _src._find_thm(name,proc2,test,false,noprefix,orig);
	}
	return {};
}
Opt<Thy> Thy::find_thy(string_view const &name, bool ancestor) const {
	size_t sep = name.find('.');
	if( sep == 0 ) {
		auto const& p = _ref->parent;
		if( !p ) throw ThyNotFound(".");
		return p->find_thy(name.substr(1));
	}
	if( auto ret = _ref->thys.finds(name) ) {
		return ret->second;
	}
	if( ancestor ) {
		if( auto& parent = _ref->parent ) {
			return parent->find_thy(name,true);
		}
	}
	return {};
}

auto _test_term_eq( Term const& x ) {
	return [&]( Term const& y ) { return x == y; };
}
bool Import::discharges( bool mod ) {
	auto x = assuming();
	if( !x ) {
		return false;
	}
	auto [name,assm] = *x;
	// if this assumption is already discharged, then reuse it
	if( auto opt = _tgt.find_thm(name,_test_term_eq(assm),true,true) ) {
		Intp::discharge(*opt);
		return true;
	}
	// if the target theory can prove the goal, then use it
	if( auto opt = proves(assm,_tgt) ) {
		Intp::discharge(*opt);
		return true;
	}
	if( mod ) { // if modification is allowed, then make new assumption
		auto thm = _tgt.add_assm(name,assm);
		Intp::discharge(thm);
		return true;
	}
	throw Error("\"failed to discharge\"")(name)(assm);
}

void Import::retain( CTerm c ) {
	auto o = obtaining();
	if( !o ) {
		throw Error(c);
	}
	auto [name,sym,ex,spec] = *o;
	Term const& stmt = spec.inst(c);
	auto const& thm = _tgt.find_thm(name,_test_term_eq(stmt),true,true);
	if(!thm) {
		throw Error(sym)(c);
	}
	Intp::retain(c,*thm);
}

bool Import::retains() {
	auto o = obtaining();
	if( !o ) {
		return false;
	}
	auto [name,sym,ex,spec] = *o;
	if( auto csym = _tgt.constant(sym) ) {
		Term const& stmt = spec.inst(*csym);
		if( auto const& thm = _tgt.find_thm(name,_test_term_eq(stmt),true,true) ) {
			Intp::retain(*csym,*thm);
			return true;
		}
		throw MalformedRetain(sym)(name)(stmt);
	} else {
		auto [sym_term,spec] = _tgt.obtain(sym,ex,name);
		retain(sym_term,spec);
		return true;
	}
}


static ostream& mk_indent(ostream& os, size_t n) {
	for( size_t i = 0; i < n; i++ ) {
		os << "  ";
	}
	return os;
}
function<ostream&(ostream&)> const Thy::print_name( Syntax const& syntax ) const& {
	return [&](ostream& os)->ostream& {
		os << _ref->name;
		if( syntax.prints_ctxt() ) {
			os << '@' << id() << ' ';
		}
		return os;
	};
}

function<ostream&(ostream&)> const Thy::pretty(Syntax const& syntax, size_t n) const & {
	return [&](ostream& os)->ostream& {
		os << "theory " << print_name(syntax);
		if( parent() ) {
			os << " <- " << parent()->print_name(syntax);
		}
		os << " {" << endl;
		n++;
		for( size_t i = 0; i < revision(); i++ ) {
			if( auto str = fixed(i) ) {
				mk_indent(os,n) << "fixes " << *str << endl;
			} else if( auto assm = assumed(i) ) {
				mk_indent(os,n) << "assumes " << syntax.pretty_thm(*assm) << endl;
			} else if( auto obt = obtained(i) ) {
				auto [sym,ex,spec] = *obt;
				mk_indent(os,n) << "obtains " << sym << " in " << syntax.pretty_thm(spec) << endl;
			} else {
				assert(false);
			}
		}
		for( auto& [name,imp] : _ref->imports ) {
			mk_indent(os,n) << "interprets" << ( imp.ready() ? " " : "[not ready]" ) << name << ": " << imp.source().print_name(syntax) << "..." << endl;
		}
		for( auto& [name,thm] : _ref->thms ) {
			mk_indent(os,n) << "thm " << name << ": " << syntax.pretty_thm(thm.first) << ';' << endl;
		}
		for( auto& [name,loc] : _ref->thys ) {
			mk_indent(os,n) << loc.pretty(syntax,n) << endl;
		}
		n--;
		return mk_indent(os,n) << "}";
	};
}
function<ostream&(ostream&)> Thy::print_thms( string_view const& name, Syntax const& syntax, string_view const& prefix ) const& {
	return [&]( ostream& os )->ostream& {
		auto fun = [&]( AThm const& thm ){
			os << prefix << syntax.pretty_thm(thm) << endl;
			return false;
		};
		find_thm(name,fun);
		return os;
	};
}
