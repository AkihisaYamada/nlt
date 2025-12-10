#include<fstream>
#include"definer.hpp"
#include"parser.hpp"

using namespace std;

string const Thy::EXACT = "#exact";
string const Thy::CONCL = "#concl";
string const Thy::INTRO = "#intro";
string const Thy::WEAK = "#weak";
string const Thy::ELIM = "#elim";
string const Thy::REWRITE = "=";

struct Thy::_Body {
	string name;
	string dir;
	Opt<Import> parent;
	StrMMap<pair<Thm,ThmInfo>> thms;
	/** local theories */
	StrMap<Thy> thys;
	Map<size_t,string> assm_names;
	multimap<string,Import,less<>> imports;
	Ref<Syntax> syntax;
	OptRef<Rewriter> rewriter;
	OptRef<Definer> definer;
	_Body( string_view const& name, string_view const& dir, Ref<Syntax> const& syntax, OptRef<Rewriter> const& rewriter, OptRef<Definer> const& definer ) : name(name), dir(dir), syntax(syntax), rewriter(rewriter), definer(definer) {
	}
	~_Body() {}
};

Thy::Thy( string_view const& name, string_view const& dir ) : _ref(Ref<_Body>::make(name,dir,Ref<Syntax>::make(),OptRef<Rewriter>(),OptRef<Definer>())) {};

Thy Thy::_branch( string_view const& name, string_view const& dir, Intp const& intp ) const {
	auto child = Thy( Ref<_Body>::make(name,dir,_ref->syntax,_ref->rewriter,_ref->definer), intp.ctxt() );
	child._ref->parent.emplace(Import(intp,*this));
	return child;
}
Thy Thy::branch() const {
	return _branch("","",Ctxt::fork());
}
Thy Thy::branch( string_view const& name, string_view const& dir ) & {
	// a bit tricky, emplace in the childs, and return a reference to it
	return _ref->thys.emplace(name,_branch(name,dir,Ctxt::fork())).first->second;
}
Thy Thy::scope_temp( string_view const& name ) const & {
	return _branch(name,"",Ctxt::self());
}
Thy Thy::scope( string_view const& name ) & {
	auto const& intp = Ctxt::self();
	auto const& loc = _branch(name,"",intp);
	add_import(name,Import(intp,loc));
	return _ref->thys.emplace(name,loc).first->second;
}

string const& Thy::name() const & {
	return _ref->name;
}
Opt<Import&> Thy::parent() & {
	return _ref->parent;
}
Opt<Import const&> Thy::parent() const & {
	return _ref->parent;
}
string const& Thy::dir() const & {
	return _ref->dir;
}
Syntax const& Thy::syntax() const& {
	return *_ref->syntax;
}
Syntax& Thy::modify_syntax() & {
	return *_ref->syntax;
}
Opt<Rewriter const&> Thy::rewriter() const& {
	if( _ref->rewriter ) {
		return {*_ref->rewriter};
	}
	return {};
}
OptRef<Rewriter>& Thy::set_rewriter() & {
	return _ref->rewriter;
}

void Thy::setup_definer( Thm const& beta ) & {
	if( _ref->definer ) throw Error("\"definer already setup\"")(beta);
	_ref->definer = OptRef<Definer>::make(*this,beta);
}
pair<string,Thm> Thy::define( Term const& fxs, Term const& r, Opt<string const&> name ) & {
	if( !_ref->definer ) throw Error("\"definer not setup\"");
	return _ref->definer->define(*this,fxs,r,name);
}

Thm Thy::thm(string_view const& name) const {
	auto opt = find_thm(name);
	if( !opt ) throw Error("\"theorem not found\"")(name);
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
	Thy const* ptr = this;
	Intp ret = Ctxt::self();
	for(;;) {
		if( *ptr == ctxt ) {
			return ret;
		}
		auto const& parent = ptr->_ref->parent;
		if( !parent ) throw Error("\"wrong ancestor\"");
		ret = parent->Intp::compose(ret);
		ptr = &parent->source();
	}
}
Thm Thy::weaken( Thm const& thm ) const {
	return thm.subst(interpret_ancestor(thm.ctxt()));
}
CTerm Thy::weaken( CTerm const& t ) const {
	return t.subst(interpret_ancestor(t.ctxt()));
}
void Thy::_check_loop_import( Thy const& origin ) const {
	if( *this == origin ) throw Error("\"looping import\"")(origin.name());
	for( auto [it,end] = _ref->imports.equal_range(""); it != end; it++ ) {
		it->second.source()._check_loop_import(origin);
	}
}
Import& Thy::add_import( string_view const& name, Import const& import ) & {
	if( import.ctxt() != *this ) throw Error("\"wrong import\"");
	if( name == "" ) {// check looping import
		import.source()._check_loop_import(*this);
	}
	return _ref->imports.emplace(name,import)->second;
};

function<Opt<Thm>(Import const&, Thm const&, ThmInfo const&)> const Thy::_triv_test =
	[]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm> {
		return {thm.subst(import)};
	};

Thm Thy::add_assm(string_view const& name, CTerm const& assm) {
	if( assm.ctxt() != *this ) throw Error("\"wrong context for add_assm\"")(assm);
	size_t rev = revision();
	_ref->assm_names.emplace(rev,name);
	return assume(assm);
}

void Thy::add_thm(string_view const& name, Thm const& thm, ThmInfo const& info) {
	if( thm.ctxt() != *this ) {
		throw Error("\"wrong context for add_thm\"")(thm);
	}
	_ref->thms.emplace(name,pair(thm,info));
}

pair<CTerm,Thm> Thy::obtain( string_view const& sym, Thm const& ex, string_view const& spec_name ) {
	size_t rev = revision();
	auto const& ret = Ctxt::obtain(sym,ex);
	add_thm(spec_name,ret.second);
	_ref->assm_names.emplace(rev,spec_name);
	return ret;
}
Opt<Thm> Thy::find_thm(
	string_view const& name,
	Import const& import,
	function<Opt<Thm>(Import const&, Thm const&, ThmInfo const&)> const& test,
	bool ancestor
) const {
	for( auto [it,end] = _ref->thms.equal_range(name); it != end; it++ ) {
		if( auto ret = test(import,it->second.first,it->second.second) ) {// found in the current theory
			return ret;
		}
	}
	auto sep = name.find('.');
	if( sep != string::npos ) {// named imports
		if( auto ret = _find_thm(name.substr(0,sep),name.substr(sep+1),import,test) ) {
			return ret;
		}
		if( sep == 0 && _ref->parent ) {// explicit parent
			return _ref->parent->source().find_thm(name.substr(1),_ref->parent->compose(import),test,ancestor);
		}
	}
	if( auto ret = _find_thm("",name,import,test) ) {// unnamed import
		return ret;
	}
	if( ancestor )
	if( auto parent = _ref->parent ) {// parent
		return parent->source().find_thm(name,parent->compose(import),test);
	}
	return {};
}
Opt<Thm> Thy::_find_thm(
	string_view const& pre,
	string_view const& name,
	Import const& import,
	function<Opt<Thm>(Import const&, Thm const&, ThmInfo const&)> const& test
) const {
	// pre as interpretations
	for( auto [it,end] = _ref->imports.equal_range(pre); it != end; it++ ) {
		auto const& prefix = it->second;
		if( prefix.ready() )
		if( auto opt = prefix._src.find_thm(name,prefix.compose(import),test,false) ) {
			return opt;
		}
	}
	return {};
}

Opt<Import> Thy::find_thy( string_view const &name, function<void(Thy&,std::istream&,std::string_view const&)> reader, bool ancestor ) {
	size_t sep = name.find('.');
	if( sep == string::npos ) {
		if( auto ret = _ref->thys.finds(name) ) {
			return {Import::make(ret->second,*this)};
		}
		if( !_ref->dir.empty() ) {
			auto path = _ref->dir+"/"+name;
			auto fullpath = path + ".nl";
			if( auto fis = fstream(fullpath) ) {
				Thy thy = branch(name,path);
				reader(thy,fis,fullpath);
				return {Import::make(thy,*this)};
			}
		}
	} else {
		for( auto [it,end] = _ref->imports.equal_range(name.substr(0,sep)); it != end; it++ ) {
			auto& im = it->second;
			if( im.ready() )
			if( auto o = im._src.find_thy(name.substr(sep+1),reader,false) ) {
				return {o->compose(im)};
			}
		}
		if( sep == 0 ) {// explicit parent
			if( auto const& p = parent() )
			if( auto o = p->_src.find_thy(name.substr(1),reader) ) {
				return {o->compose(*p)};
			}
		}
	}
	for( auto [it,end] = _ref->imports.equal_range(""); it != end; it++ ) {
		auto& im = it->second;
		if( im.ready() )
		if( auto o = im._src.find_thy(name,reader,false) ) {
			return {o->compose(im)};
		}
	}
	if( ancestor )
	if( auto const& p = parent() )
	if( auto o = p->_src.find_thy(name,reader) ) {
		return {o->compose(*p)};
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
function<ostream&(ostream&)> Thy::print_name( bool ancestors ) const& {
	if( ancestors ) {
		return [&](ostream& os)->ostream& {
			list<Thy const*> path;
			auto p = parent();
			while(p) {
				auto const& thy = p->source();
				path.push_front(&thy);
				p = thy.parent();
			}
			for( auto& pre : path ) {
				if( pre->name() == "" ) {
					os << '@' << pre->id();
				} else {
					os << pre->name();
				}
				os << '/';
			}
			os << _ref->name;
			if( syntax().prints_ctxt() || _ref->name == "" ) {
				os << '@' << id();
			}
			return os;
		};
	} else {
		return [&](ostream& os)->ostream& {
			return os << _ref->name;
		};
	}
}

function<ostream&(ostream&)> Thy::pretty( size_t n, bool scope, bool path ) const & {
	return [&n,scope,path,this](ostream& os)->ostream& {
		n++;
		if( scope ) {
			os << "namespace " << print_name(path) << ':' << endl;
		} else {
			os << "theory " << print_name(path) << ':' << endl;
			for( size_t i = 0; i < revision(); ) {
				if( auto str = fixed(i) ) {
					mk_indent(os,n) << "fixes";
					do {
						os << ' ' << pretty_sym(*str);
						i++;
					} while( str = fixed(i) );
					os << '.' << endl;
				}
				if( auto assm = assumed(i) ) {
					mk_indent(os,n) << "assumes ";
					if( auto name = find_assm_name(i) ) {
						os << *name << ": ";
					}
					os << pretty(*assm) << '.' << endl;
					i++;
					continue;
				}
				if( auto obt = obtained(i) ) {
					auto [sym,ex,spec] = *obt;
					mk_indent(os,n) << "obtains ";
					if( auto name = find_assm_name(i) ) {
						os << *name;
					}
					os << ": " << pretty(spec) << '.' << endl;
					i++;
					continue;
				}
				break;
			}
		}
		for( auto& [name,imp] : _ref->imports ) {
			mk_indent(os,n) << "interprets " << name << ": " << imp.pretty() << endl;
		}
		for( auto& [name,thm] : _ref->thms ) {
			mk_indent(os,n) << "thm " << name << ": " << pretty(thm.first) << '.' << endl;
		}
		for( auto& [name,thy] : _ref->thys ) {
			mk_indent(os,n) << thy.pretty( n, (Ctxt const&)thy == *this, false ) << endl;
		}
		n--;
		return mk_indent(os,n) << "end";
	};
}
function<ostream&(ostream&)> Thy::print_thms( string_view const& name, string_view const& prefix ) const& {
	return [&]( ostream& os )->ostream& {
		auto fun = [&]( Import const& import, Thm const& thm, ThmInfo const& )->Opt<Thm>{
			os << prefix << pretty(thm.subst(import)) << endl;
			return {};
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
				os << punc << _src.pretty(sym) << " := " << _src.pretty(*term);
				punc = ", ";
			}
		}
		return os << '.';
	};
}