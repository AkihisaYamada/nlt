#include"definer.hpp"

using namespace std;

struct Thy::_Body {
	string name;
	string dir;
	Opt<Import> parent;
	StrMMap<pair<Thm,ThmInfo>> thms;
	StrMap<Thy> thys;
	Map<size_t,string> assm_names;
	multimap<string,Import,less<>> imports;
	Mem<Rewriter> rewriter;
	OptMem<Definer> definer;
	_Body( string_view const& name, string_view const& dirname ) : name(name), dir(dirname), rewriter(Mem<Rewriter>::make()) {}
};

Thy::Thy( string_view const& name, string_view const& dirname ) : _ref(Ref<_Body>::make(name,dirname)) {};

Thy Thy::branch() const {
	auto intp = Ctxt::branch();
	auto child = Thy( Ref<_Body>::make("",""), intp.ctxt() );
	child._ref->parent = Import(intp,child,*this);
	return child;
}
Thy Thy::branch( string_view const& name, string_view const& dirname ) {
	auto intp = Ctxt::branch();
	auto child = Thy( Ref<_Body>::make(name,dirname), intp.ctxt() );
	child._ref->parent = Import(intp,child,*this);
	_ref->thys.emplace(name,child);
	return child;
}
Thy Thy::scope( string_view const& name ) const {
	auto child = Thy( Ref<_Body>::make(name,""), *this );
	child._ref->parent = self();
	return child;
}
string const& Thy::name() const & {
	return _ref->name;
}
Opt<Thy const&> Thy::parent() const & {
	if( auto const& imp = _ref->parent ) {
		return {imp->source()};
	}
	return {};
}
Opt<Thy&> Thy::parent() & {
	if( auto& imp = _ref->parent ) {
		return {imp->source()};
	}
	return {};
}
string const& Thy::dir() const & {
	return _ref->dir;
}
Opt<AThm> Thy::find_thm(
	string_view const& name,
	function<bool(AThm const&)> const& test
) const {
	return _find_thm(name,test,self());
}
Rewriter const& Thy::rewriter() const& {
	return *_ref->rewriter;
}
Rewriter& Thy::rewriter() & {
	return *_ref->rewriter;
}
void Thy::setup_definer( Thm const& beta ) & {
	if( _ref->definer ) throw Error("\"definer already setup\"")(beta);
	_ref->definer = OptMem<Definer>::make(*this,beta);
}
pair<string,Thm> Thy::define( Term const& fxs, Term const& r, Opt<string const&> name ) & {
	if( !_ref->definer ) throw Error("\"definer not setup\"");
	return _ref->definer->define(*this,fxs,r,name);
}

AThm Thy::thm(string_view const& name) const {
	auto opt = find_thm(name);
	if( !opt ) throw TheoremNotFound(name);
	return *opt;
}
Opt<string> Thy::find_assm_name( size_t rev ) const {
	if( auto x = _ref->assm_names.finds(rev) ) {
		return {x->second};
	}
	return {};
}
StrMMap<Import> const& Thy::imports() const {
	return _ref->imports;
}
Opt<Import&> Thy::import_parent() const & {
	return _ref->parent;
}

Import& Thy::import(string_view const& name, Import const& prefix, Thy const& loc) & {
auto imp = Import(prefix.interpret(loc),*this,loc);
	auto it = _ref->imports.emplace(name,imp);
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
		throw Error("\"wrong context for add_thm\"")(thm);
	}
	_ref->thms.emplace(name,pair(thm,info));
	return AThm(self(),thm,info);
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
	function<bool(AThm const&)> const& test,
	Import const& import
) const {
	for( auto [it,end] = _ref->thms.equal_range(name); it != end; it++ ) {
		auto const& ret = AThm(import,it->second.first,it->second.second);
		if( test(ret) ) {// found in the current theory
			return ret;
		}
	}
	auto sep = name.find('.');
	if( sep == 0 ) {// explicit parent
		auto parent = _ref->parent;
		if( !parent ) throw Error("\"parent theory not found\"");
		return parent->_find_thm(name.substr(1),test,import.compose(*parent));
	}
	if( sep != string::npos ) {// named imports
		if( auto ret = _find_thm(name.substr(0,sep),name.substr(sep+1),test,import) ) {
			return ret;
		}
	}
	if( auto ret = _find_thm("",name,test,import) ) {// unnamed import
		return ret;
	}
	return {};
}
Opt<AThm> Thy::_find_thm(
	string_view const& pre,
	string_view const& name,
	function<bool(AThm const&)> const& test,
	Import const& import
) const {
	// pre as interpretations
	for( auto [it,end] = _ref->imports.equal_range(pre); it != end; it++ ) {
		auto const& suffix = it->second;
		if( suffix.ready() )
		if( auto opt = suffix._src._find_thm(name,test,import.compose(suffix)) ) {
			return opt;
		}
	}
	return {};
}

Opt<Thy> Thy::find_thy(string_view const &name) const {
	size_t sep = name.find('.');
	if( sep == 0 ) {
		auto const& p = _ref->parent;
		if( !p ) throw ThyNotFound(".");
		return p->_src.find_thy(name.substr(1));
	}
	if( name == _ref->name ) {
		return *this;
	}
	if( auto ret = _ref->thys.finds(name) ) {
		return ret->second;
	}
	return {};
}

auto _test_term_eq( Term const& x ) {
	return [&]( Term const& y ) { return x == y; };
}

static ostream& mk_indent(ostream& os, size_t n) {
	for( size_t i = 0; i < n; i++ ) {
		os << "  ";
	}
	return os;
}
function<ostream&(ostream&)> const Thy::print_name( Syntax const& syntax ) const& {
	return [&](ostream& os)->ostream& {
		list<string> pres;
		auto p = parent();
		while(p) {
			pres.push_front(p->name());
			p = p->parent();
		}
		for( auto& pre : pres ) {
			os << pre << '.';
		}
		os << _ref->name;
		if( syntax.prints_ctxt() ) {
			os << '@' << id() << ' ';
		}
		return os;
	};
}

function<ostream&(ostream&)> const Thy::pretty(Syntax const& syntax, size_t n) const & {
	return [&](ostream& os)->ostream& {
		if( name() == "" ) {
			os << endl;
		} else {
			os << "theory " << print_name(syntax) << ":" << endl;
		}
		n++;
		for( size_t i = 0; i < revision(); i++ ) {
			if( auto str = fixed(i) ) {
				mk_indent(os,n) << "fixes " << *str << '.' << endl;
			} else if( auto assm = assumed(i) ) {
				mk_indent(os,n) << "assumes " << *find_assm_name(i) << ": " << syntax.pretty_thm(*assm) << '.' << endl;
			} else if( auto obt = obtained(i) ) {
				auto [sym,ex,spec] = *obt;
				mk_indent(os,n) << "obtains ";
				if( auto name = find_assm_name(i) ) {
					os << *name;
				}
				os << ": " << syntax.pretty_term(spec) << '.' << endl;
			} else {
				assert(false);
			}
		}
		for( auto& [name,imp] : _ref->imports ) {
			mk_indent(os,n) << "interprets " << name << ": " << imp.pretty(syntax) << endl;
		}
		for( auto& [name,thm] : _ref->thms ) {
			mk_indent(os,n) << "thm " << name << ": " << syntax.pretty_thm(thm.first) << '.' << endl;
		}
		for( auto& [name,thy] : _ref->thys ) {
			mk_indent(os,n) << thy.pretty(syntax,n) << endl;
		}
		n--;
		return mk_indent(os,n) << "end";
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
function<ostream&(ostream&)> const Import::pretty(Syntax const& syntax, size_t indent) const & {
	return [&]( ostream& os )->ostream& {
		if( _src.name() == "" ) {
			return os << _src.pretty(syntax,indent+1);
		}
		os << _src.name();
		if( !ready() ) {
			os << "[not ready]";
		}
		string punc = "; ";
		for( auto [sym,term] : Intp::subst().map() ) {
			if( term ) {
				os << punc << sym << " := " << syntax.pretty_term(*term);
				punc = ", ";
			}
		}
		return os << '.';
	};
}