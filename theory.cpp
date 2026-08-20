#include<fstream>
#include <limits>
#include<sstream>
#include<ranges>
#include"theory.hpp"

using namespace std;

string const NONREC_IMPORT = "#nonrec";
string const ANONYM_THY = "#anonym";

struct Thy::_Body {
	string name;
	std::filesystem::path dir;
	StrMMap<Pair<Thm,ThmInfo>> thms;
	StrMap<Map<Term,Pair<Thm,ThmInfo>>> term_thms;
	/** local theories */
	StrMap<Thy> thys;
	Map<size_t,string> assm_names;
	Opt<Import> parent;
	StrMMap<Pair<Import,bool>> imports;
	Ref<Syntax> syntax;
	StrMap<Pair<Ref<Rewrite>,bool>> rewriter;
	bool is_scope;
	_Body( string_view const& name, std::filesystem::path const& dir, bool is_scope, Ref<Syntax> const& syntax ) : name(name), dir(dir), is_scope(is_scope), syntax(syntax) {
	}
	~_Body() {}
};

Thy::Thy( string_view const& name, std::filesystem::path const& dir ) :
	_ref(Ref<_Body>::make(name,dir,false,Ref<Syntax>::make())) {};

Thy Thy::_branch( string_view const& name, std::filesystem::path const& dir, bool is_scope, Intp const& intp ) const& {
	auto child = Thy( Ref<_Body>::make(name,dir,is_scope,_ref->syntax), intp.ctxt() );
	child._ref->parent.emplace(Import(intp,*this));
	for( auto [rew_name,p] : _ref->rewriter ) {
		child._ref->rewriter.emplace(rew_name,{p.first,false});
	}
	return child;
}
Thy Thy::branch() const& {
	return _branch(ANONYM_THY,"",false,Ctxt::fork());
}
Thy Thy::branch( string_view const& name, filesystem::path const& dir ) {
	auto const& [it,fl] = _ref->thys.emplace(name,_branch(name,dir,false,Ctxt::fork()));
	if( !fl ) throw Error("\"duplicate theory\"")(path())(name);
	return it->second;
}
Thy Thy::scope_temp( string_view const& name ) const {
	return _branch(name,"",true,Ctxt::self());
}
Thy Thy::scope( string_view const& name ) {
	auto const& intp = Ctxt::self();
	return add_import(name,Import(intp,_branch(name,"",true,intp)),true,false,false).source();
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
std::filesystem::path const& Thy::dir() const & {
	return _ref->dir;
}
Syntax const& Thy::syntax() const& {
	return *_ref->syntax;
}
Syntax& Thy::modify_syntax() & {
	return *_ref->syntax;
}
Opt<Rewrite const&> Thy::find_rewriter( string_view const& rew_name ) const& {
	if( auto x = _ref->rewriter.finds_value(rew_name) ) {
		return {*x->first};
	}
	return {};
}
Rewrite& Thy::modify_rewriter( string_view const& rew_name ) & {
	auto x = _ref->rewriter.finds_value(rew_name);
	if( !x ) {
		auto [it,b] = _ref->rewriter.emplace(rew_name,{Ref<Rewrite>::make(Rewrite()),true});
		return *it->second.first;
	}
	if( !x->second ) {
		x->first = Ref<Rewrite>::make(*x->first);// copy rewriter
		x->second = true;
	}
	return *x->first;
}
void Thy::reset_rewrite() & {
	for( auto& [rew_name,val] : _ref->rewriter ) {
		auto& [rew,own] = val;
		if( !own )
		if( auto const& p = parent() ) {
			rew = p->source()._ref->rewriter.finds_value(rew_name)->first;
		}
	}
}
void Thy::import_rewrite( Import const& import, bool override_default ) & {
	Thy const& src = import.source();
	for( auto& [rew_name,val] : src._ref->rewriter ) {
		auto& rew = modify_rewriter(rew_name);
		rew.import(*val.first,src,import,false);
	}
}
Thm Thy::thm( string_view const& name ) const {
	auto opt = find_thm(name);
	if( !opt ) throw Error("\"theorem not found\"")(name);
	return *opt;
}
Opt<string> Thy::find_assm_name( size_t rev ) const {
	return _ref->assm_names.finds_value(rev);
}

StrMMap<Pair<Import,bool>> const& Thy::imports() const {
	return _ref->imports;
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
void Thy::check_loop_import( Thy const& origin, bool rec ) const {
	if( *this == origin ) throw Error("\"looping import\"")(origin.path());
	for( auto [it,end] = _ref->imports.equal_range(""); it != end; it++ ) {
		auto const& [im,rec2] = it->second;
		im.source().check_loop_import(origin,rec);
	}
	if( rec ) {
		for( auto [it,end] = _ref->imports.equal_range(NONREC_IMPORT); it != end; it++ ) {
			auto const& [im,rec2] = it->second;
			im.source().check_loop_import(origin,rec2);
		}
	}
}
Import& Thy::add_import( string_view const& prefix, Import const& import, bool rec, bool override, bool rewrite ) & {
	if( import.ctxt() != *this ) throw Error("\"wrong import\"")(path());
	if( prefix.empty() ) {
		import.source().check_loop_import(*this,rec);// check looping import
		if( rewrite ) {
			import_rewrite(import,override);
		}
	}
	return (override ?
		_ref->imports.emplace_front(prefix,{import,rec}) :
		_ref->imports.emplace_back(prefix,{import,rec})
	)->second.first;
}
void Thy::erase_import( string_view const& prefix ) & {
	_ref->imports.erase_front(prefix);
}
Thy::ThmTest const Thy::_triv_test =
	[]( Import const& import, std::string_view const& name, Thm const& thm, ThmInfo const& info )->Opt<Thm> {
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
	_ref->thms.emplace_front(name,{thm,info});
}

Pair<CTerm,Thm> Thy::obtain( string_view const& sym, Thm const& ex, string_view const& spec_name, bool declare ) {
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
	ThmTest const& test
) const {
	return _find_thm(name,self(),test,true,true);
}
Opt<Thm> Thy::_find_thm(
	string_view const& path,
	Import const& import,
	ThmTest const& test,
	bool allow_ancestor,
	bool allow_rec
) const {
	auto sep = path.find('.');
	if( sep == 0 ) {// explicit parent
		if( auto p = parent() ) {
			return p->source()._find_thm(path.substr(1),p->compose(import),test,allow_ancestor,allow_rec);
		}
		return {};
	} else if( sep != string::npos ) {// qualified imports
		return _find_thm(path.substr(0,sep),path.substr(sep+1),import,test,allow_ancestor,allow_rec);
	} else {// unprefixed; find from local theorems
		return _find_thm_name(path,import,test,allow_ancestor,allow_rec);
	}
}
Opt<Thm> Thy::_find_thm_name(
	string_view const& name,
	Import const& import,
	ThmTest const& test,
	bool allow_ancestor,
	bool allow_rec
) const {
	if( auto ret = _find_thm_local(name,import,test) ) return ret;
	return _find_thm_unqualified(name,import,test,allow_ancestor,allow_rec);
}
Opt<Thm> Thy::_find_thm_local(
	string_view const& name,
	Import const& import,
	ThmTest const& test
) const {
	// find from local theorems
	if( name == "" ) {
		for( auto const& [name,athm] : _ref->thms ) {
			if( auto ret = test(import,name,athm.first,athm.second) ) {
				return ret;
			}
		}
	} else {
		for( auto [it,end] = _ref->thms.equal_range(name); it != end; it++ ) {
			if( auto ret = test(import,name,it->second.first,it->second.second) ) {
				return ret;
			}
		}
	}
	return {};
}

Opt<Thm> Thy::_find_thm_unqualified(
	string_view const& name,
	Import const& import,
	ThmTest const& test,
	bool allow_ancestor,
	bool allow_rec
) const {
	auto f = [&]( auto const& fst_end )->Opt<Thm> {
		for( auto [it,end] = fst_end; it != end; it++ ) {
			auto const& [p,rec] = it->second;
			if( p.ready() )
			if( auto ret = p._src._find_thm_name(name,p.compose(import),test,false,rec) ) {
				return ret;
			}
		}
		return {};
	};
	if( auto ret = f(_ref->imports.equal_range("")) ) {
		return ret;
	}
	if( allow_rec )// find from unnamed imports
	if( auto ret = f(_ref->imports.equal_range(NONREC_IMPORT)) ) {
		return ret;
	}
	if( allow_ancestor )// find from ancestors
	if( auto p = parent() ) {
		return p->source()._find_thm_name(name,p->compose(import),test,true,true);
	}
	return {};
}
Opt<Thm> Thy::_find_thm(
	string_view const& pre,
	string_view const& rest,
	Import const& import,
	ThmTest const& test,
	bool allow_ancestor,
	bool allow_rec
) const {
	if( pre == _ref->name )// explict self
	if( auto ret = _find_thm(rest,import,test,false,true) ) {
		return ret;
	}
	// find from local imports
	for( auto [it,end] = _ref->imports.equal_range(pre); it != end; it++ ) {
		auto const& [p,rec] = it->second;
		if( p.ready() )
		if( auto ret = p._src._find_thm(rest,p.compose(import),test,false,rec) ) {
			return ret;
		}
	}
	auto g = [&]( auto const& it_end )->Opt<Thm> {
		for( auto [it,end] = it_end; it != end; it++ ) {
			auto const& [p,rec] = it->second;
			if( p.ready() )
			if( auto ret = p._src._find_thm(pre,rest,p.compose(import),test,false,rec) ) {
				return ret;
			}
		}
		return {};
	};
	// find from recursive unqualified imports
	if( auto ret = g(_ref->imports.equal_range("")) ) {
		return ret;
	}
	if( allow_rec )// find from unqualified imports
	if( auto ret = g(_ref->imports.equal_range(NONREC_IMPORT)) ) {
		return ret;
	}
	if( allow_ancestor )// find from ancestors
	if( auto p = parent() )
	if( auto ret = p->source()._find_thm(pre,rest,p->compose(import),test,true,true) ) {
		return ret;
	}
	return {};
}
void Thy::add_term_thm( Term const& t, std::string const& prop, Thm const& thm, ThmInfo const& info ) & {
	assert( thm.ctxt() == *this );
	auto [it,fl] = _ref->term_thms.emplace(prop,{});
	auto& map = it->second;
	map.emplace(t,Pair<Thm,ThmInfo>(thm,info));
}

Opt<Pair<Thm,ThmInfo>> Thy::_find_term_thm( Term const& s, std::string const& prop, Import const& import, bool allow_rec ) & {
	if( auto map = _ref->term_thms.finds_value(prop) ) {
		for( auto const& [t,val] : *map ) {
			if( t.subst(import) == s ) {// TODO: implement equal modulo substitution
				auto const& [thm,info] = val;
				return {{thm.subst(import),info}};
			}
		}
	}
	// find from imports
	auto f = [&]( auto const& it )->Opt<Pair<Thm,ThmInfo>>{
		auto const& [p,rec] = it->second;
		if( p.ready() )
		if( auto ret = p.source()._find_term_thm(s.subst(import),prop,p.compose(import),rec) ) {
			return ret;
		}
		return {};
	};
	for( auto [it,end] = _ref->imports.equal_range(""); it != end; it++ ) {
		if( auto ret = f(it) ) return ret;
	}
	if( allow_rec ) {
		for( auto [it,end] = _ref->imports.equal_range(NONREC_IMPORT); it != end; it++ ) {
			if( auto ret = f(it) ) return ret;
		}
	}
	return {};
}
Opt<Pair<Thm,ThmInfo> const&> Thy::find_term_thm( Term const& s, std::string const& prop ) & {
	// find from local database
	auto [pair,fresh] = _ref->term_thms.emplace(prop,{});
	if( !fresh ) {
		if( auto ret = pair->second.finds_value(s) ) {
			return ret;
		}
	}
	for( auto [it,end] = _ref->imports.equal_range(""); it != end; it++ ) {
		auto const& [p,rec] = it->second;
		if( p.ready() )
		if( auto ret = p.source()._find_term_thm(s,prop,p,rec) ) {
			auto [it,fl] = pair->second.emplace(s,*ret);
			return {it->second};
		}
	}
	for( auto [it,end] = _ref->imports.equal_range(NONREC_IMPORT); it != end; it++ ) {
		auto const& [p,rec] = it->second;
		if( auto ret = p.source()._find_term_thm(s,prop,p,rec) ) {
			auto [it,fl] = pair->second.emplace(s,*ret);
			return {it->second};
		}
	}
	if( auto const& p = parent() )
	if( auto ret = p->source().find_term_thm(s,prop) ) {
		auto const& [thm,info] = *ret;
		auto [it,fl] = pair->second.emplace(s,Pair<Thm,ThmInfo>(weaken(thm),info));
		return {it->second};
	}
	return {};
}

Opt<Import> Thy::find_thy(
	string_view const& path,
	function<void(Thy&,std::istream&,std::string_view const&)> const& reader,
	std::function<bool(Thy const&)> const& test
) {
	return _find_thy(path,reader,test,true,true);
}
Opt<Import> Thy::_find_thy(
	string_view const& path,
	function<void(Thy&,istream&,string_view const&)> const& reader,
	std::function<bool(Thy const&)> const& test,
	bool allow_ancestor,
	bool allow_rec
) {
	size_t sep = path.find('.');
	if( sep == 0 ) {// explicit parent
		if( auto const& p = parent() ) {
			if( auto o = p->_src._find_thy(path.substr(1),reader,test,allow_ancestor,allow_rec) ) {
				return o->compose(*p);
			}
		}
	} else if( sep != string::npos ) {// explicit prefix
		if( auto ret = _find_thy(path.substr(0,sep),path.substr(sep+1),reader,test,allow_ancestor,allow_rec) ) {
			return ret;
		}
	} else {// unprefixed
		if( auto ret = _find_thy_name(path,reader,test,allow_ancestor,allow_rec) ) {
			return ret;
		}
	}
	return {};
}
Opt<Import> Thy::_find_thy_name(
	string_view const& name,
	function<void(Thy&,istream&,string_view const&)> const& reader,
	function<bool(Thy const&)> const& test,
	bool allow_ancestor,
	bool allow_rec
) {
	if( auto ret = _ref->thys.finds_value(name) ) {// find from local theories
		if( test(*ret) ) return {Import::make(*ret,*this)};
	}
	if( !_ref->dir.empty() ) {// load from theory directory
		auto dirpath = _ref->dir+"/"+name;
		auto fullpath = dirpath + ".nl";
		if( auto fis = fstream(fullpath) ) {
			Thy thy = branch(name,dirpath);
			reader(thy,fis,fullpath);
			if( test(thy) ) return {Import::make(thy,*this)};
		}
	}
	auto f = [&]( auto const& it_end )->Opt<Import> {
		for( auto [it,end] = it_end; it != end; it++ ) {
			auto const& [p,rec] = it->second;
			if( p.ready() )
			if( auto o = p._src._find_thy_name(name,reader,test,false,rec) ) {
				return o->compose(p);
			}
		}
		return {};
	};
	// find from recursive unnamed imports
	if( auto ret = f(_ref->imports.equal_range("")) ) {
		return ret;
	}
	if( allow_rec )// find from unnamed imports
	if( auto ret = f(_ref->imports.equal_range(NONREC_IMPORT)) ) {
		return ret;
	}
	if( allow_ancestor )// find from parent
	if( auto const& p = parent() )
	if( auto o = p->_src._find_thy_name(name,reader,test,allow_ancestor,true) ) {
		return o->compose(*p);
	}
	return {};
}
Opt<Import> Thy::_find_thy(
	string_view const& pre,
	string_view const& rest,
	function<void(Thy&,istream&,string_view const&)> const& reader,
	std::function<bool(Thy const&)> const& test,
	bool allow_ancestor,
	bool allow_rec
) & {
	if( pre == _ref->name )// explict self
	if( auto ret = _find_thy(rest,reader,test,false,true) ) {
		return ret;
	}
	// find from local imports
	for( auto [it,end] = _ref->imports.equal_range(pre); it != end; it++ ) {
		auto const& [p,rec] = it->second;
		if( p.ready() )
		if( auto o = p._src._find_thy(rest,reader,test,false,rec) ) {
			return {o->compose(p)};
		}
	}
	auto g = [&]( auto const& it_end )->Opt<Import> {
		for( auto [it,end] = it_end; it != end; it++ ) {// find from unqualified imports
			auto const& [p,rec] = it->second;
			if( p.ready() )
			if( auto o = p._src._find_thy(pre,rest,reader,test,false,rec) ) {
				return {o->compose(p)};
			}
		}
		return {};
	};
	if( auto ret = g(_ref->imports.equal_range("")) ) {
		return ret;
	}
	if( allow_rec )
	if( auto ret = g(_ref->imports.equal_range(NONREC_IMPORT)) ) {
		return ret;
	}
	if( allow_ancestor )
	if(	auto p = parent() )
	if( auto o = p->_src._find_thy(pre,rest,reader,test,true,true) ) {
		return {o->compose(*p)};
	}
	return {};
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
				os << pre->name() << '/';
			}
			os << _ref->name;
			if( syntax().prints_ctxt() || _ref->name == ANONYM_THY ) {
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

string Thy::path() const& {
	std::ostringstream oss;
	oss << print_path();
	return oss.str();
}
ostream& Thy::pretty(
	ostream& os,
	function<ostream&(ostream&)> const& endl,
	bool thms, unsigned short n, bool scope, bool path, bool print_rewrite
) const & {
	unsigned short n1 = n+1;
	if( scope ) {
		os << "namespace " << print_path(path) << ':' << endl;
	} else {
		os << ( thms ? "theory " : "context " ) << print_path(path) << " :=" << endl;
		size_t fini = finalized().value_or(std::numeric_limits<size_t>::max());
		for( size_t i = 0;; ) {
			if( i == fini ) {
				os << mk_indent(n) << "begin" << endl;
			}
			if( auto str = fixed_at(i) ) {
				os << mk_indent(n1) << "fix";
				do {
					os << ' ' << pretty_sym(*str);
					i++;
				} while( str = fixed_at(i) );
				os << '.' << endl;
			}
			if( auto assm = assumed_at(i) ) {
				os << mk_indent(n1) << "assume ";
				if( auto name = find_assm_name(i) ) {
					os << *name << ": ";
				}
				os << pretty(*assm) << '.' << endl;
				i++;
				continue;
			}
			if( auto obt = obtained_at(i) ) {
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
	if( thms ) {
		for( auto const& [name,pair] : _ref->imports ) {
			auto const& [im,rec] = pair;
			os << mk_indent(n1) << "interpret " << name <<
				( rec ? "! " : name.empty() ? "" : ": " ) << im.pretty() << endl;
		}
		for( auto const& [name,thm] : _ref->thms ) {
			os << mk_indent(n1) << "thm " << name << ": " << pretty(thm.first) << '.' << endl;
		}
		for( auto const& [name,thy] : _ref->thys ) {
			os << mk_indent(n1) << thy.pretty( endl, true, n1, (Ctxt const&)thy == *this, false ) << endl;
		}
		if( print_rewrite ) {
			for( auto const& [name,rew] : _ref->rewriter ) {
				os << pretty_rewrite(*rew.first,n1,[&](ostream&os)->ostream&{ return os << "rewriter " << name; },endl);
			}
		}
	}
	return os << mk_indent(n) << "end";
}
ostream& Thy::pretty_rewrite(
	ostream& os,
	Rewrite const& rew,
	size_t n,
	function<ostream&(ostream&)> const& prefix,
	function<ostream&(ostream&)> const& endl
) const & {
	size_t n1 = n+1;
	auto const& rels = rew.rels();
	for( size_t i = 0; i < rels.size(); i++ ) {
		auto const& rel = rels[i];
		os << mk_indent(n) << prefix << "[on " << rel;
		if( rew._default_rel.contains(rel) ) os << ", default";
		os << ']' << endl << mk_indent(n1) << "refl: " << pretty( rew.get_refl(i) ) << endl;
		if( auto fallback = rew._fallbacks.finds_value(i) ) {
			os << mk_indent(n1) << "fallback: " << pretty(*fallback) << endl;
		}
	}
	return os;
}

function<ostream&(ostream&)> Thy::print_thms( string_view const& name, string_view const& prefix ) const& {
	return [&]( ostream& os )->ostream& {
		auto fun = [&]( Import const& import, string_view const& rname, Thm const& thm, ThmInfo const& )->Opt<Thm>{
			os << prefix << rname << ": " << pretty(thm.subst(import)) << endl;
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