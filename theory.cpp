#include<fstream>
#include<ranges>
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
	vector<Import> prior_imports;// prior imports
	vector<Import> post_imports;// posterior imports
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
		if( !own )
		if( auto const& p = parent() ) {
			rew = p->source()._ref->rewriter.finds(rew_name)->second.first;
		}
	}
}
void Thy::import_rewrite( Import const& import ) & {
	Thy const& src = import.source();
	for( auto& [rew_name,val] : src._ref->rewriter ) {
		auto& rew = modify_rewriter(rew_name);
		rew.import(*val.first,src,import);
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
vector<Import> const& Thy::prior_imports() const {
	return _ref->prior_imports;
}
vector<Import> const& Thy::post_imports() const {
	return _ref->post_imports;
}
bool Thy::has_ancestor( Ctxt const& ctxt ) const & {
	Thy const* ptr = this;
	for(;;) {
		if( *ptr == ctxt ) {
			return true;
		}
		auto const& parent = ptr->parent();
		if( !parent ) return false;
		ptr = &parent->source();
	}
	return false;
}
Intp Thy::interpret_ancestor( Ctxt const& ctxt ) const & {
	Thy const* ptr = this;
	Intp ret = Ctxt::self();
	for(;;) {
		if( *ptr == ctxt ) {
			return ret;
		}
		auto const& parent = ptr->parent();
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
Import& Thy::_add_import( Import const& import, bool prior ) & {
	if( import.ctxt() != *this ) throw Error("\"wrong import\"");
	import.source()._check_loop_import(*this);// check looping import
	import_rewrite(import);
	return (prior ? _ref->prior_imports : _ref->post_imports).emplace_back(import);
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
		return parent()->source().add_assm( _ref->name+'.'+name, assm );
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
	auto sep = name.find('.');
	if( sep == 0 ) {// explicit parent
		auto p = parent();
		if( !p ) return {};
		return p->_src._find_thm(name.substr(1),p->compose(import),test,allow_ancestor );
	} else if( sep != string::npos ) {// qualified imports
		if( auto ret = _find_thm(name.substr(0,sep),name.substr(sep+1),import,test) ) {
			return ret;
		}
	} else {// unprefixed; find from local theorems
		for( auto [fst,it] = _ref->thms.equal_range(name); it != fst; ) {
			it--;
			if( auto ret = test(import,it->second.first,it->second.second) ) {// found in the current theory
				return ret;
			}
		}
	}
	auto f = [&]( Import const& pre )->Opt<Thm>{
		if( pre.ready() ) {
			return {pre._src._find_thm(name,pre.compose(import),test,false)};
		}
		return {};
	};
	// find from prior imports
	for( auto const& pre : std::views::reverse(_ref->prior_imports) ) {
		if( auto ret = f(pre) ) return ret;
	}
	// find from posterior imports
	for( auto const& pre : _ref->post_imports ) {
		if( auto ret = f(pre) ) return ret;
	}
	// find from parent
	if( allow_ancestor )
	if( auto p = parent() )
	if( auto ret = p->source()._find_thm(name,p->compose(import),test,true) ) {
		return ret;
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
	function<void(Thy&,std::istream&,std::string_view const&)> const& reader,
	std::function<bool(Thy const&)> const& test
) {
	if( auto ret = _find_thy(path,reader,true,false,test) ) {
		return ret;
	}
	return _find_thy(NONREC_IMPORT,path,reader,false,test);
}

Opt<Import> Thy::find_thy_local(
	string_view const& path,
	function<void(Thy&,std::istream&,std::string_view const&)> const& reader,
	std::function<bool(Thy const&)> const& test
) {
	auto f = [&]( Thy const& thy )->Opt<Import> {
		if( test(thy) ) return {Import::make(thy,*this)};
		return {};
	};
	if( auto ret = _ref->thys.finds(path) ) {
		auto const& thy = ret->second;
		assert( thy.name() == path );
		return f(thy);
	}
	if( !_ref->dir.empty() ) {
		auto filepath = _ref->dir+"/"+path;
		auto fullpath = filepath + ".nl";
		if( auto fis = fstream(fullpath) ) {
			Thy thy = branch(path,filepath);
			reader(thy,fis,fullpath);
			return f(thy);
		}
	}
	return {};
}

Opt<Import> Thy::find_import( std::function<bool(Thy const&)> const& test ) {
	if( test(*this) ) return {self()};
	for( auto const& im : _ref->prior_imports ) {
		if( auto o = im.source().find_import(test) ) {
			return {o->compose(im)};
		}
	}
	for( auto const& im : _ref->post_imports ) {
		if( auto o = im.source().find_import(test) ) {
			return {o->compose(im)};
		}
	}
	if( auto const& p = parent() )
	if( auto const& o = p->source().find_import(test) ) {
		return {o->compose(*p)};
	}
	return {};
}
Opt<Import> Thy::_find_thy(
	string_view const& path,
	function<void(Thy&,std::istream&,std::string_view const&)> const& reader,
	bool allow_ancestor,
	bool import_source,
	std::function<bool(Thy const&)> const& test
) {
	size_t sep = path.find('.');
	if( sep == string::npos ) {
		if( import_source ) {
			for( auto [fst,it] = _ref->qualified_imports.equal_range(path); it != fst; ) {
				it--;
				auto const& im = it->second;
				if( im.ready() ) {
					if( test(im._src) ) {
						return {im};
					}
					if( auto o = im._src.find_import(test) ) {
						return {o->compose(im)};
					}
				}
			}
		} else {
			if( auto ret = find_thy_local(path,reader,test) ) {
				return ret;
			}
		}
	} else if( sep == 0 ) {// explicit parent
		auto p = parent();
		if( !p ) return {};
		if( auto o = p->_src._find_thy(path.substr(1),reader,true,import_source,test) ) {
			return {o->compose(*p)};
		}
	} else {// explicit prefix
		if( auto ret = _find_thy(path.substr(0,sep),path.substr(sep+1),reader,import_source,test) ) {
			return ret;
		}
	}
	auto f = [&]( Import const& pre )->Opt<Import>{
		if( pre.ready() )
		if( auto o = pre._src._find_thy(path,reader,false,import_source,test) ) {
			return {o->compose(pre)};
		}
		return {};
	};
	// find from unqualified imports
	for( auto& pre : std::views::reverse(_ref->prior_imports) ) {
		if( auto ret = f(pre) ) return ret;
	}
	for( auto& pre : _ref->post_imports ) {
		if( auto ret = f(pre) ) return ret;
	}
	// find from parent
	if( allow_ancestor )
	if( auto const& p = parent() )
	if( auto o = p->_src._find_thy(path,reader,allow_ancestor,import_source,test) ) {
		return {o->compose(*p)};
	}
	return {};
}

Opt<Import> Thy::_find_thy(
	string_view const& pre,
	string_view const& rest,
	function<void(Thy&,istream&,string_view const&)> const& reader,
	bool import_source,
	std::function<bool(Thy const&)> const& test
) & {
	for( auto [fst,it] = _ref->qualified_imports.equal_range(pre); it != fst; ) {
		it--;
		auto const& im = it->second;
		if( im.ready() )
		if( auto o = im._src._find_thy(rest,reader,false,import_source,test) ) {
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
	size_t n1 = n+1;
	if( scope ) {
		os << "namespace " << print_path(path) << ':' << endl;
	} else {
		os << "theory " << print_path(path) << ':' << endl;
		for( size_t i = 0; i < revision(); ) {
			if( auto str = fixed(i) ) {
				os << mk_indent(n1) << "fix";
				do {
					os << ' ' << pretty_sym(*str);
					i++;
				} while( str = fixed(i) );
				os << '.' << endl;
			}
			if( auto assm = assumed(i) ) {
				os << mk_indent(n1) << "assume ";
				if( auto name = find_assm_name(i) ) {
					os << *name << ": ";
				}
				os << pretty(*assm) << '.' << endl;
				i++;
				continue;
			}
			if( auto obt = obtained(i) ) {
				auto [sym,ex,spec] = *obt;
				os << mk_indent(n1) << "obtain ";
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
	os << mk_indent(n) << "begin" << endl;
	for( auto const& imp : _ref->prior_imports ) {
		os << mk_indent(n1) << "interpret " << imp.pretty() << endl;
	}
	for( auto const& imp : _ref->post_imports ) {
		os << mk_indent(n1) << "interpret? " << imp.pretty() << endl;
	}
	for( auto const& [name,imp] : _ref->qualified_imports ) {
		os << mk_indent(n1) << "interpret " << name << ": " << imp.pretty() << endl;
	}
	for( auto const& [name,thm] : _ref->thms ) {
		os << mk_indent(n1) << "thm " << name << ": " << pretty(thm.first) << '.' << endl;
	}
	for( auto const& [name,thy] : _ref->thys ) {
		os << mk_indent(n1) << thy.pretty( endl, n1, (Ctxt const&)thy == *this, false ) << endl;
	}
	for( auto const& [name,rew] : _ref->rewriter ) {
		os << pretty_rewrite(
			[&]( ostream& os )->ostream&{
				return os << mk_indent(n) << "rewriter " << name;
			},
			[&]( ostream& os )->ostream&{ return os << endl << mk_indent(n); },
			*rew.first
		);
	}
	return os << mk_indent(n) << "end";
}
ostream& Thy::pretty_rewrite(
	ostream& os,
	function<ostream&(ostream&)> const& prefix,
	function<ostream&(ostream&)> const& endl,
	Rewrite const& rew
) const & {
	auto const& rels = rew.rels();
	for( size_t i = 0; i < rels.size(); i++ ) {
		auto const& rel = rels[i];
		os << prefix << '[' << i << "] for (" << rel << ") " << endl
			<< "  refl: " << pretty( rew.get_refl(i) ) << endl;
		if( auto trans = rew._trans.finds(i) ) {
			os << "  trans: " << pretty(trans->second) << endl;
		}
		if( auto fallback = rew._fallbacks.finds(i) ) {
			os << "  fallback: " << pretty(fallback->second) << endl;
		}
	}
	return os;
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