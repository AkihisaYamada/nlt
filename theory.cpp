#include<fstream>
#include"definer.hpp"

using namespace std;

struct Thy::_Body {
	string name;
	string dir;
	Opt<Import> parent;
	StrMMap<pair<Thm,ThmInfo>> thms;
	/** local theories */
	StrMap<Thy> thys;
	Map<size_t,string> assm_names;
	multimap<string,Import,less<>> imports;
	Mem<Syntax> syntax;
	Mem<Rewriter> rewriter;
	OptMem<Definer> definer;
	_Body( string_view const& name, string_view const& dirname, Mem<Syntax> const& syntax, Mem<Rewriter> const& rewriter, Mem<Definer> const& definer ) : name(name), dir(dirname), syntax(syntax), rewriter(rewriter), definer(definer) {}
};

Thy::Thy( string_view const& name, string_view const& dirname ) : _ref(Ref<_Body>::make(name,dirname,Mem<Syntax>::make(),Mem<Rewriter>::make(),Mem<Definer>::make())) {};

Import const& Thy::branch() const {
	auto intp = Ctxt::branch();
	auto child = Thy( Ref<_Body>::make("","",_ref->syntax,_ref->rewriter,_ref->definer), intp.ctxt() );
	return child._ref->parent.emplace(Import(intp,child,*this));
}
Import const& Thy::branch( string_view const& name, string_view const& dirname ) {
	auto intp = Ctxt::branch();
	auto child = Thy( Ref<_Body>::make(name,dirname,_ref->syntax,_ref->rewriter,_ref->definer), intp.ctxt() );
	_ref->thys.emplace(name,child);
	return child._ref->parent.emplace(Import(intp,child,*this));
}
Thy Thy::scope( string_view const& name ) const {
	auto child = Thy( Ref<_Body>::make(name,"",_ref->syntax,_ref->rewriter,_ref->definer), *this );
	child._ref->parent = self();
	return child;
}
string const& Thy::name() const & {
	return _ref->name;
}
Opt<Import const&> Thy::parent() const & {
	return _ref->parent;
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
Syntax const& Thy::syntax() const& {
	return *_ref->syntax;
}
Syntax& Thy::syntax() & {
	return *_ref->syntax;
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
Intp Thy::interpret_ancestor( Ctxt const& ctxt ) const & {
	Intp ret = Ctxt::self();
	for(;;) {
		if( ctxt == *this ) {
			return ret;
		}
		auto p = _ref->parent;
		if( !p ) throw Error("\"wrong ancestor\"");
		ret = ret.compose(*p);
	}
}
Thm Thy::weaken( Thm const& thm ) const {
	return thm.subst(interpret_ancestor(thm.ctxt()));
}
CTerm Thy::weaken( CTerm const& t ) const {
	return t.subst(interpret_ancestor(t.ctxt()));
}
Import& Thy::add_import( string_view const& name, Import const& import ) & {
	if( import.thy() != *this ) throw Error("\"wrong import\"");
	return _ref->imports.emplace(name,import)->second;
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

Opt<Import> Thy::find_thy( string_view const &name, function<Thy(Thy const&,fstream&)> reader ) {
	size_t sep = name.find('.');
	if( sep != string::npos ) {
		for( auto [it,end] = _ref->imports.equal_range(name.substr(0,sep)); it != end; it++ ) {
			auto& prefix = it->second;
			if( prefix.ready() )
			if( auto ret = prefix._src.find_thy(name.substr(sep+1),reader) ) {
				return {prefix.compose(*ret)};
			}
		}
	} else {
		if( auto ret = _ref->thys.finds(name) ) {
			return {self().import(ret->second)};
		}
		if( !_ref->dir.empty() ) {
			auto path = _ref->dir+"/"+name;
			if( auto fis = fstream(path+".nl") ) {
				auto ret = branch(name,path);
				reader(ret.thy(),fis);
				return {ret};
			}
		}
	}
	if( auto& p = parent() )
	if( auto ret = p->_src.find_thy(name,reader) ) {
		return {p->compose(*ret)};
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
function<ostream&(ostream&)> const Thy::print_name() const& {
	return [&](ostream& os)->ostream& {
		list<string> pres;
		auto p = parent();
		while(p) {
			pres.push_front(p->thy().name());
			p = p->thy().parent();
		}
		for( auto& pre : pres ) {
			os << pre << '.';
		}
		os << _ref->name;
		if( syntax().prints_ctxt() ) {
			os << '@' << id() << ' ';
		}
		return os;
	};
}

function<ostream&(ostream&)> const Thy::pretty( size_t n ) const & {
	return [&](ostream& os)->ostream& {
		if( name() == "" ) {
			os << endl;
		} else {
			os << "theory " << name() << ":" << endl;
		}
		n++;
		for( size_t i = 0; i < revision(); i++ ) {
			if( auto str = fixed(i) ) {
				mk_indent(os,n) << "fixes " << *str << '.' << endl;
			} else if( auto assm = assumed(i) ) {
				mk_indent(os,n) << "assumes " << *find_assm_name(i) << ": " << pretty_thm(*assm) << '.' << endl;
			} else if( auto obt = obtained(i) ) {
				auto [sym,ex,spec] = *obt;
				mk_indent(os,n) << "obtains ";
				if( auto name = find_assm_name(i) ) {
					os << *name;
				}
				os << ": " << pretty_term(spec) << '.' << endl;
			} else {
				assert(false);
			}
		}
		for( auto& [name,imp] : _ref->imports ) {
			mk_indent(os,n) << "interprets " << name << ": " << imp.pretty() << endl;
		}
		for( auto& [name,thm] : _ref->thms ) {
			mk_indent(os,n) << "thm " << name << ": " << pretty_thm(thm.first) << '.' << endl;
		}
		for( auto& [name,thy] : _ref->thys ) {
			mk_indent(os,n) << thy.pretty(n) << endl;
		}
		n--;
		return mk_indent(os,n) << "end";
	};
}
function<ostream&(ostream&)> Thy::print_thms( string_view const& name, string_view const& prefix ) const& {
	return [&]( ostream& os )->ostream& {
		auto fun = [&]( AThm const& thm ){
			os << prefix << pretty_thm(thm) << endl;
			return false;
		};
		find_thm(name,fun);
		return os;
	};
}
function<ostream&(ostream&)> const Import::pretty( size_t indent ) const & {
	return [&]( ostream& os )->ostream& {
		if( _src.name() == "" ) {
			return os << _src.pretty(indent+1);
		}
		os << _src.name();
		if( !ready() ) {
			os << "[not ready]";
		}
		string punc = "; ";
		for( auto [sym,term] : Intp::subst().map() ) {
			if( term ) {
				os << punc << sym << " := " << _src.pretty_term(*term);
				punc = ", ";
			}
		}
		return os << '.';
	};
}