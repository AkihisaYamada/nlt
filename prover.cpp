#include<fstream>
#include"util.hpp"
#include"syntax.hpp"

using namespace std;

struct ProverFailure : exception {
	String message;
	ProverFailure(String const& message) : message(message) {}
};
class UnfinishedProof : std::exception {};

class Prover {
	struct Thesis {
		Ctxt ctxt;
		Term claim;
	};
	unsigned int _depth;
	Ctxt _ctxt;
	bool _own_syntax;
	Ref<Syntax> _syntax;
	optional<Thesis> _thesis;
	optional<Ref<Rewriter>> _rewriter;
	optional<Ref<Definer>> _definer;
	bool _exit_on_error;
public:
	Prover(istream& is, bool exit_on_error) :
		_depth(0),
		_ctxt(),
		_syntax(is),
		_own_syntax(true),
		_exit_on_error(exit_on_error) {
		_ctxt.fix(IMP_var);
		_ctxt.fix(ALL_var);
		_syntax->register_single_op(',');
		_syntax->register_single_op(';');
		_syntax->register_multi_op(':');
		_syntax->register_multi_op('*');
		_syntax->register_multi_op('+');
		_syntax->infix(",",-1,-1,-2).
			infix(";",-1,-1,-2);
	}
	Prover(Prover const& parent, optional<Thesis> thesis = optional<Thesis>()) :
		_depth(parent._depth+1),
		_ctxt(parent._ctxt.branch()),
		_syntax(parent._syntax),
		_own_syntax(false),
		_thesis(thesis),
		_rewriter(parent._rewriter) {}
	Prover(Prover const& parent, Term const& claim) : Prover(parent,Thesis{parent._ctxt,claim}) {}

	Thm get_thm() {
		Ctxt loc = _ctxt.branch();
		optional<Thm> thm = _gets_thm(loc);
		if( !thm.has_value() ) {
			throw Syntax::Error("expects a theorem");
		}
		return thm->intro();
	}

	optional<Thm> _gets_thm(Ctxt loc) {
		auto const& opt = _syntax->gets_thm_name();
		if( !opt.has_value() ) {
			return optional<Thm>();
		}
		Thm ret = loc.thm(*opt);
		for(;;) {
			if( _syntax->skips("(") ) {
				do {
					ret = ret.allE(loc.enclose(_syntax->get_term()));
				} while( _syntax->skips(",") );
				_syntax->skip(")");
			} else if( _syntax->skips("[") ) {
				if( _syntax->skips("OF") ) {
					for(;;) {
						auto const& opt_arg = _gets_thm(loc);
						if( !opt_arg.has_value() ) {
							break;
						}
						ret = discharge(ret,*opt_arg);
					}
				} else if( _syntax->skips("rewrite") ) {
					bool many = _syntax->skips("*");
					Rewriter::Rules rules;
					for(;;) {
						auto const& opt_arg = _gets_thm(loc);
						if( !opt_arg.has_value() ) {
							break;
						}
						rules.add(*opt_arg);
					}
					if( many ) {
						ret = (**_rewriter).normalize(rules,ret,255);
					} else {
						auto const& opt_ret = (**_rewriter).rewrite(rules,ret);
						if( !opt_ret.has_value() ) {
							throw ProverFailure("Failed rewrite");
						}
						ret = *opt_ret;
					}
				}
				_syntax->skip("]");
			} else {
				return ret;
			}
		}
	}

	StrMap<Thm> get_named_thms() {
		StrMap<Thm> ret;
		for(;;) {
			optional<String> name = _syntax->gets_thm_name();
			if( !name.has_value() ) {
				break;
			}
			_syntax->skip(":");
			Thm thm = get_thm();
			ret.insert({*name,thm});
		}
		return ret;
	}
	Term get_term() {
		Term term = _syntax->get_term();
		if( _syntax->skips("$") ) {
			CSubst subst = _ctxt.branch();
			do {
				String sym = _syntax->get_token();
				_syntax->skip(":=");
				subst.assign(sym,get_term());
			} while( _syntax->skips(",") );
			term = term.subst(subst);
		}
		return term;
	}

	vector<pair<String,Term>> get_named_terms() {
		vector<pair<String,Term>> ret;
		for(;;) {
			optional<String> name = _syntax->gets_thm_name();
			if( !name.has_value() ) {
				break;
			}
			_syntax->skip(":");
			ret.push_back({*name,_syntax->get_term()});
			if( !_syntax->skips(",") ) {
				break;
			}
		}
		return ret;
	}

	optional<Thm> loop() {
		for(;;) try {
			for( int i = 0; i <= _depth; i++ ) {
				cout << '>';
			}
			cout << ' ' << flush;
			if( _syntax->skips("{") ) {
				cout << "Creating context." << endl;
				Prover(*this).loop();
				_syntax->skip("}");
				cout << "Left context." << endl;
			} else if( _syntax->skips("ctxt") ) {
				_syntax->skip(";");
				cout << _syntax->pretty_ctxt(_ctxt) << endl;
			} else if( _syntax->skips("fix") ) {
				cout << "Fixing";
				for(;;) {
					if( _syntax->skips(";") ) break;
					String sym = _syntax->get_token();
					_ctxt.fix(sym);
					cout << ' ' << sym << flush;
				}
				cout << ';' << endl;
			} else if( _syntax->skips("assume") ) {
				cout << "Assuming ";
				for(;;) {
					String name = _syntax->get_thm_name();
					_syntax->skip(":");
					Term term = _syntax->gets_term(0).value();
					cout << name << ": " << _syntax->pretty_term(term) << flush;
					_ctxt.assume(name,term);
					if( !_syntax->skips(",") ) {
						break;
					}
					cout << ", " << flush;
				}
				_syntax->skip(";");
				cout << endl;
			} else if( _syntax->skips("thm") ) {
				Thm thm = get_thm();
				_syntax->skip(";");
				cout << "thm " << _syntax->pretty_thm(thm) << endl;
			} else if( _syntax->skips("term") ) {
				Term term = get_term();
				_syntax->skip(";");
				cout << "term " << _syntax->pretty_term(term) << endl;
			} else if( _syntax->skips("name") ) {
				String name = _syntax->get_thm_name();
				_syntax->skip(":");
				_ctxt.claim(name,get_thm());
				_syntax->skip(";");
				cout << "lemma " << name << ": " << _syntax->pretty_thm(_ctxt.thm(name)) << endl;
			} else if( _syntax->skips("move") ) {
				Ctxt pctxt = *_ctxt.find_ctxt();
				String name = _syntax->get_thm_name();
				_syntax->skip(":");
				pctxt.claim(name,get_thm().intro());
				_syntax->skip(";");
				cout << "theorem " << name << ": " << _syntax->pretty_thm(pctxt.thm(name)) << endl;
			} else if( _syntax->skips("show") ) {
				String thm_name = _syntax->get_thm_name();
				_syntax->skip(":");
				CTerm stmt = _ctxt.cterm(_syntax->get_term(0));
				_syntax->skip(";");
				cout << "Proving " << thm_name << ": " << _syntax->pretty_term(stmt) << endl;
				auto const& prf = Prover(*this,stmt).loop();
				if( !prf.has_value() ) {
					cout << "ERROR: Nothing proved." << endl;
					throw UnfinishedProof();
				}
				Ctxt stmt_ctxt = _ctxt.branch();
				CTerm stmt_strip = strip_all(stmt,stmt_ctxt);
				Thm thm = prf->intro();
				Ctxt thm_ctxt = stmt_ctxt.branch();
				Thm thm_strip = strip_all(thm,thm_ctxt);
				stmt_strip = stmt_strip.weaken(thm_ctxt);
				optional<CSubst> matcher = match(thm_ctxt.syms(),thm_strip,stmt_strip);
				if( !matcher.has_value() ) {
					cout << "ERROR: Proof mismatch " << _syntax->pretty_term(thm) << endl;
					throw UnfinishedProof();
				}
				thm = thm.weaken(stmt_ctxt);
				for( auto const& v : thm_ctxt.sym_list() ) {
					thm = thm.allE(matcher->get(v)->lift(stmt_ctxt));
				}
				thm = thm.intro();
				_ctxt.claim(thm_name,thm);
			} else if( _syntax->skips("obtain") ) {
				String sym = _syntax->get_token();
				_syntax->skip("where");
				auto specs = get_named_terms();
				_syntax->skip(";");
				Ctxt obtainer = _ctxt.obtain(sym,specs);
				Term const& goal = obtainer.assms()[0];
				cout << "Obtaining " << sym << " where ";
				for( auto& spec : specs ) {
					cout << spec.first << ": " << _syntax->pretty_term(spec.second) << ", ";
				}
				cout << endl << "Proving " << _syntax->pretty_term(goal) << endl;
				auto const& prf = Prover(*this,goal).loop();
				if( !prf.has_value() ) {
					cout << "ERROR: Nothing proved." << endl;
					throw UnfinishedProof();
				}
				Thm goal_thm = prf->intro();
				if( goal != goal_thm ) {
					cout << "ERROR: Proof mismatch " << _syntax->pretty_term(goal_thm) << endl;
					throw UnfinishedProof();
				}
				obtainer = obtainer.interpret(CSubst(_ctxt),{goal_thm});
				_ctxt.import(obtainer);
				cout << "Obtained " << sym << endl;
			} else if( _syntax->skips("define") ) {
				optional<String> name;
				if( _syntax->skips("(") ) {
					name = _syntax->get_token();
					_syntax->skip(")");
				}
				Term rule = get_term();
				_syntax->skip(";");
				(**_definer).define(_ctxt,rule,name);
				cout << "Defined " << _syntax->pretty_term(rule) << endl;
			} else if( _syntax->skips("by") ) {
				if( !_thesis.has_value() ) {
					cerr << "No goal for \"by\"" << endl;
					throw UnfinishedProof();
				}
				Thm ret = get_thm();
				_syntax->skip(";");
				cerr << "By " << _syntax->pretty_thm(ret) << endl;
				return ret;
			} else if( _syntax->skips("prefix") ) {
				String sym = _syntax->get_token();
				int rlevel = _syntax->get_int();
				int level = _syntax->get_int();
				_syntax->skip(";");
				_make_own_syntax();
				_syntax->prefix(sym,level,rlevel);
				cout << "New prefix operator " << sym << endl;
			} else if( _syntax->skips("infix") ) {
				String sym = _syntax->get_token();
				int llevel = _syntax->get_int();
				int rlevel = _syntax->get_int();
				int level = _syntax->get_int();
				_syntax->skip(";");
				_make_own_syntax();
				_syntax->infix(sym,level,llevel,rlevel);
				cout << "New infix operator " << sym << endl;
			} else if( _syntax->skips("setup") ) {
				if( _syntax->skips("rewrite") ) {
					auto const& thms = get_named_thms();
					_rewriter = Ref(Rewriter(thms));
					cout << "Setup Rewrite Axioms:" << endl << _syntax->pretty_thms(thms) << endl;
				} else if( _syntax->skips("define") ) {
					String const& eq = _syntax->get_token();
					String const& lam = _syntax->get_token();
					Thm const& beta = get_thm();
					cerr << "equality: " << eq << " lambda: " << lam << " beta: " << _syntax->pretty_thm(beta) << endl;
					_definer = optional(Definer(**_rewriter,eq,lam,beta));
				}
				_syntax->skip(";");
			} else if( _syntax->skips("symbol") ) {
				while( !_syntax->skips(";") ) {
					string const& sym = _syntax->get_token();
					_syntax->register_multi_op(int_of_chars(sym.data()));
				}
			} else {
				return optional<Thm>();
			}
		} catch ( MalformedDischarge const& e ) {
			cerr << "ERROR: Discharging\n\t" << _syntax->pretty_term(e.imp) << endl << "with\t" << _syntax->pretty_term(e.arg) << endl;
			exit(-1);
		} catch ( MalformedInstantiation const& e ) {
			cerr << "ERROR: Instantiating\n\t" << _syntax->pretty_term(e.all) << endl << "with\t" << _syntax->pretty_term(e.arg) << endl;
			exit(-1);
		} catch ( TheoremNotFound const& e ) {
			cerr << "ERROR: No thm \"" << e.name << "\" found" << endl;
			exit(-1);
		} catch ( UnexpectedTerm const& e ) {
			cerr << "ERROR: Unexpected term " << _syntax->pretty_term(e.term) << endl;
			exit(-1);
		} catch ( UnboundVariable const& e ) {
			cerr << "ERROR: Unbound variable " << e.name << endl;
			exit(-1);
		} catch ( Syntax::Error const& e ) {
			cerr << "Syntax ERROR: " << e.message << endl;
			exit(-1);
		}
	}
private:
	void _make_own_syntax() {
		if( !_own_syntax ) {
			_syntax = Ref(*_syntax);
			_own_syntax = true;
		}
	}
};

int main(int argc, char* argv[]) {
	istream* pis;
	bool exit_on_error = false;
	if( argc == 1 ) {
		pis = &cin;
	} else {
		pis = new fstream(argv[1]);
		exit_on_error = true;
	}
	Prover prover = Prover(*pis,exit_on_error);
	prover.loop();
	cout << "bye!" << endl;
	return 0;
}

