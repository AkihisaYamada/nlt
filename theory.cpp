#include<fstream>
#include"theory.hpp"
#include"parser.hpp"

using namespace std;

string const NONREC_IMPORT = "#nonrec";

struct Thy::_Body {
	string name;
	string dir;
	Opt<Import> parent;
	StrMMap<pair<Thm,ThmInfo>> thms;
	/** local theories */
	StrMap<Thy> thys;
	Map<size_t,string> assm_names;
	multimap<string,Import,less<>> qualified_imports;
	deque<Import> unqualified_imports;
	Ref<Syntax> syntax;
	StrMap<pair<Ref<Rewrite>,bool>> rewriter;
	bool is_scope;
	_Body( string_view const& name, string_view const& dir, bool is_scope, Ref<Syntax> const& syntax ) : name(name), dir(dir), is_scope(is_scope), syntax(syntax) {
	}
	~_Body() {}
};

Thy::Thy( string_view const& name, string_view const& dir ) : _ref(Ref<_Body>::make(name,dir,false,Ref<Syntax>::make())) {};

Thy Thy::_branch( string_view const& name, string_view const& dir, bool is_scope, Intp const& intp ) const& {
	auto child = Thy( Ref<_Body>::make(name,dir,is_scope,_ref->syntax), intp.ctxt() );
	child._ref->parent.emplace(Import(intp,*this));
	for( auto [rew_name,p] : _ref->rewriter ) {
		child._ref->rewriter.emplace(rew_name,pair(p.first,false));
	}
	return child;
}
Thy Thy::branch() const& {
	return _branch("","",false,Ctxt::fork());
}
Thy Thy::branch( string_view const& name, string_view const& dir ) {
	return _ref->thys.emplace(name,_branch(name,dir,false,Ctxt::fork())).first->second;
}
Thy Thy::scope_temp( string_view const& name ) const {
	return _branch(name,"",true,Ctxt::self());
}
Thy Thy::scope( string_view const& name ) {
	auto const& intp = Ctxt::self();
	return add_import(name,Import(intp,_branch(name,"",true,intp))).source();
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
Opt<Rewrite const&> Thy::find_rewriter( string_view const& rew_name ) const& {
	if( auto x = _ref->rewriter.finds(rew_name) ) {
		return {*x->second.first};
	}
	return {};
}
Rewrite& Thy::modify_rewriter( string_view const& rew_name ) & {
	auto x = _ref->rewriter.finds(rew_name);
	if( !x ) {
		auto [it,b] = _ref->rewriter.emplace(rew_name,pair{Ref<Rewrite>::make(Rewrite()),true});
		return *it->second.first;
	}
	if( !x->second.second ) {
		x->second.first = Ref<Rewrite>::make(*x->second.first);
		x->second.second = true;
	}
	return *x->second.first;
}
void Thy::reset_rewrite() & {
	for( auto& [rew_name,val] : _ref->rewriter ) {
		auto& [rew,own] = val;
		if( !own && _ref->parent ) {
			rew = _ref->parent->source()._ref->rewriter.finds(rew_name)->second.first;
		}
	}
}
void Thy::import_rewrite( Thy const& src, Intp const& intp ) & {
	for( auto& [rew_name,val] : src._ref->rewriter ) {
		auto& rew = modify_rewriter(rew_name);
		rew.import(*val.first,src,intp);
	}
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
	return _ref->qualified_imports;
}
deque<Import> const& Thy::unqualified_imports() const {
	return _ref->unqualified_imports;
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
	for( auto [it,end] = _ref->qualified_imports.equal_range(""); it != end; it++ ) {
		it->second.source()._check_loop_import(origin);
	}
}
Import& Thy::add_import( string_view const& prefix, Import const& import ) & {
	if( import.ctxt() != *this ) throw Error("\"wrong import\"");
	return _ref->qualified_imports.emplace(prefix,import)->second;
}
Import& Thy::add_import( Import const& import, bool prior ) & {
	if( import.ctxt() != *this ) throw Error("\"wrong import\"");
	import.source()._check_loop_import(*this);// check looping import
	if( prior ) {
		return _ref->unqualified_imports.emplace_front(import);
	} else {
		return _ref->unqualified_imports.emplace_back(import);
	}
}
void Thy::erase_import( string_view const& prefix ) & {
	auto [it,end] = _ref->qualified_imports.equal_range(prefix);
	_ref->qualified_imports.erase(it,end);
}
function<Opt<Thm>(Import const&, Thm const&, ThmInfo const&)> const Thy::_triv_test =
	[]( Import const& import, Thm const& thm, ThmInfo const& info )->Opt<Thm> {
		return {thm.subst(import)};
	};

Thm Thy::add_assm( string_view const& name, CTerm const& assm ) {
	if( _ref->is_scope ) {
		assert(_ref->parent);
		return _ref->parent->source().add_assm( _ref->name+'.'+name, assm );
	}
	if( assm.ctxt() != *this ) throw Error("\"wrong context for add_assm\"")(assm);
	size_t rev = revision();
	_ref->assm_names.emplace(rev,name);
	return assume(assm);
}

void Thy::add_thm( string_view const& name, Thm const& thm, ThmInfo const& info ) & {
	if( thm.ctxt() != *this ) {
		throw Error("\"wrong context for add_thm\"")(thm);
	}
	_ref->thms.emplace(name,pair(thm,info));
}

pair<CTerm,Thm> Thy::obtain( string_view const& sym, Thm const& ex, string_view const& spec_name, bool declare ) {
	size_t rev = revision();
	auto const& ret = Ctxt::obtain(sym,ex);
	_ref->assm_names.emplace(rev,spec_name);
	if( declare ) {
		add_thm(spec_name,ret.second);
	}
	return ret;
}
Opt<Thm> Thy::find_thm(
	string_view const& name,
	function<Opt<Thm>(Import const&, Thm const&, ThmInfo const&)> const& test
) const {
	auto import = self();
	if( auto ret = _find_thm(name,import,test,true) ) {
		return ret;
	}
	return _find_thm(NONREC_IMPORT,name,import,test);// non-recursive import
}

Opt<Thm> Thy::_find_thm(
	string_view const& name,
	Import const& import,
	function<Opt<Thm>(Import const&, Thm const&, ThmInfo const&)> const& test,
	bool allow_ancestor
) const {
	// find from local
	if( auto sep = name.find('.'); sep != string::npos ) {// named imports
		if( auto ret = _find_thm(name.substr(0,sep),name.substr(sep+1),import,test) ) {
			return ret;
		}
		if( sep == 0 && _ref->parent ) {// explicit parent
			return _ref->parent->source()._find_thm(name.substr(1),_ref->parent->compose(import),test,allow_ancestor);
		}
	} else {// unprefixed; find from local theorems
		for( auto [fst,it] = _ref->thms.equal_range(name); it != fst; ) {
			it--;
			if( auto ret = test(import,it->second.first,it->second.second) ) {// found in the current theory
				return ret;
			}
		}
	}
	// find from unqualified imports
	for( auto const& prefix : _ref->unqualified_imports ) {
		if( prefix.ready() )
		if( auto opt = prefix._src._find_thm(name,prefix.compose(import),test,false) ) {
			return opt;
		}
	}
	// find from parent
	if( allow_ancestor )
	if( auto parent = _ref->parent ) {
		return parent->source()._find_thm(name,parent->compose(import),test,true);
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
	for( auto [fst,it] = _ref->qualified_imports.equal_range(pre); it != fst; ) {
		it--;
		auto const& prefix = it->second;
		if( prefix.ready() )
		if( auto opt = prefix._src._find_thm(name,prefix.compose(import),test,false) ) {
			return opt;
		}
	}
	return {};
}

Opt<Import> Thy::find_thy(
	string_view const& path,
	function<void(Thy&,std::istream&,std::string_view const&)> reader,
	bool allow_ancestor
) {
	if( auto ret = _find_thy(path,reader,allow_ancestor) ) {
		return ret;
	}
	return _find_thy(NONREC_IMPORT,path,reader);
}
Opt<Import> Thy::find_thy_local(
	string_view const& name,
	function<void(Thy&,istream&,string_view const&)> reader
) {
	if( auto ret = _ref->thys.finds(name) ) {
		assert( ret->second.name() == name );
		return {Import::make(ret->second,*this)};
	}
	if( !_ref->dir.empty() ) {
		auto filepath = _ref->dir+"/"+name;
		auto fullpath = filepath + ".nl";
		if( auto fis = fstream(fullpath) ) {
			Thy thy = branch(name,filepath);
			reader(thy,fis,fullpath);
			return {Import::make(thy,*this)};
		}
	}
	return {};
}

Opt<Import> Thy::_find_thy( string_view const& path, function<void(Thy&,std::istream&,std::string_view const&)> reader, bool allow_ancestor ) {
	size_t sep = path.find('.');
	if( sep == string::npos ) {
		if( auto ret = find_thy_local(path,reader) ) {
			return ret;
		}
	} else if( sep == 0 ) {// explicit parent
		if( auto const& p = parent() )
		if( auto o = p->_src._find_thy(path.substr(1),reader,allow_ancestor) ) {
			return {o->compose(*p)};
		}
	} else {
		if( auto ret = _find_thy(path.substr(0,sep),path.substr(sep+1),reader) ) {
			return ret;
		}
	}
	// find from unqualified imports
	for( auto& imp : _ref->unqualified_imports ) {
		if( imp.ready() )
		if( auto o = imp._src._find_thy(path,reader,false) ) {
			return {o->compose(imp)};
		}
	}
	// find from parent
	if( allow_ancestor )
	if( auto const& p = parent() )
	if( auto o = p->_src.find_thy(path,reader) ) {
		return {o->compose(*p)};
	}
	return {};
}

Opt<Import> Thy::_find_thy(
	string_view const& pre,
	string_view const& rest,
	function<void(Thy&,istream&,string_view const&)> reader
) & {
	for( auto [fst,it] = _ref->qualified_imports.equal_range(pre); it != fst; ) {
		it--;
		auto const& im = it->second;
		if( im.ready() )
		if( auto o = im._src._find_thy(rest,reader,false) ) {
			return {o->compose(im)};
		}
	}
	return {};
}

auto _test_term_eq( Term const& x ) {
	return [&]( Term const& y ) { return x == y; };
}

static function<ostream&(ostream&)> mk_indent( size_t n ) {
	return [n]( ostream& os )->ostream& {
		for( size_t i = 0; i < n; i++ ) {
			os << "  ";
		}
		return os;
	};
}
function<ostream&(ostream&)> Thy::print_path( bool ancestors ) const& {
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

ostream& Thy::pretty(
	ostream& os,
	function<ostream&(ostream&)> const& endl, size_t n, bool scope, bool path
) const & {
	n++;
	if( scope ) {
		os << "namespace " << print_path(path) << ':' << endl;
	} else {
		os << "theory " << print_path(path) << ':' << endl;
		for( size_t i = 0; i < revision(); ) {
			if( auto str = fixed(i) ) {
				os << mk_indent(n) << "fixes";
				do {
					os << ' ' << pretty_sym(*str);
					i++;
				} while( str = fixed(i) );
				os << '.' << endl;
			}
			if( auto assm = assumed(i) ) {
				os << mk_indent(n) << "assumes ";
				if( auto name = find_assm_name(i) ) {
					os << *name << ": ";
				}
				os << pretty(*assm) << '.' << endl;
				i++;
				continue;
			}
			if( auto obt = obtained(i) ) {
				auto [sym,ex,spec] = *obt;
				os << mk_indent(n) << "obtains ";
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
	for( auto& imp : _ref->unqualified_imports ) {
		os << mk_indent(n) << "interprets " << imp.pretty() << endl;
	}
	for( auto& [name,imp] : _ref->qualified_imports ) {
		os << mk_indent(n) << "interprets " << name << ": " << imp.pretty() << endl;
	}
	for( auto& [name,thm] : _ref->thms ) {
		os << mk_indent(n) << "thm " << name << ": " << pretty(thm.first) << '.' << endl;
	}
	for( auto& [name,thy] : _ref->thys ) {
		os << mk_indent(n) << thy.pretty( endl, n+1, (Ctxt const&)thy == *this, false ) << endl;
	}
	return os << mk_indent(n-1) << "end";
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
function<ostream&(ostream&)> Import::pretty( function<ostream&(ostream&)> const& endl, size_t indent ) const & {
	return [&]( ostream& os )->ostream& {
		if( _src.name() == "" ) {
			indent++;
			return os << _src.pretty(endl,indent);
		}
		os << _src.print_path(true);
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