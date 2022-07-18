#include <fstream>
#include "syntax.hpp"

using namespace std;

class UnfinishedProof : std::exception {};

class Prover {
	struct Thesis {
		Ctxt ctxt;
		Term claim;
	};
	Ctxt ctxt;
	bool own_syntax;
	Ref<Syntax> syntax;
	optional<Thesis> thesis;
public:
	Prover(istream& is) : syntax(is), own_syntax(true) {
		syntax->infix(",",-1,-1,-2).
			infix(";",-1,-1,-2);
	}
	Prover(Prover const& parent, string_view name = "") :
		ctxt(parent.ctxt.branch()),
		syntax(parent.syntax),
		own_syntax(false),
		thesis(optional<Thesis>()) {}
	Prover(Prover const& parent, string_view thm_name, Term const& claim) :
		ctxt(parent.ctxt.branch()),
		syntax(parent.syntax),
		own_syntax(false),
		thesis({parent.ctxt,claim}) {}

	optional<Thm> loop() {
		for(;;) try {
			cout << "> " << flush;
			if( syntax->skips('{') ) {
				cout << "Creating context." << endl;
				Prover(*this).loop();
				syntax->skip('}');
				cout << "Left context." << endl;
			} else if( syntax->skips("ctxt") ) {
				syntax->skip(';');
				cout << syntax->pretty_ctxt(ctxt) << endl;
			} else if( syntax->skips("fix") ) {
				cout << "Fixing";
				for(;;) {
					if( syntax->skips(';') ) break;
					string sym = syntax->get_token();
					ctxt.fix(sym);
					cout << ' ' << sym << flush;
				}
				cout << ';' << endl;
			} else if( syntax->skips("assume") ) {
				cout << "Assuming ";
				for(;;) {
					string name = syntax->get_thm_name();
					syntax->skip(':');
					Term term = syntax->get_term(0).value();
					cout << name << ": " << syntax->pretty_term(term) << flush;
					ctxt.assume(name,term);
					if( !syntax->skips(',') ) {
						break;
					}
					cout << ", " << flush;
				}
				syntax->skip(';');
				cout << ';' << endl;
			} else if( syntax->skips("thm") ) {
				Thm thm = syntax->get_thm(ctxt);
				syntax->skip(';');
				cout << "thm " << syntax->pretty_thm(thm) << endl;
			} else if( syntax->skips("term") ) {
				Term term = syntax->get_term(0).value();
				syntax->skip(';');
				cout << "term " << syntax->pretty_term(term) << endl;
			} else if( syntax->skips("name") ) {
				string name = syntax->get_thm_name();
				syntax->skip(':');
				ctxt.claim(name,syntax->get_thm(ctxt));
				syntax->skip(';');
				cout << "lemma " << name << ": " << syntax->pretty_thm(ctxt.thm(name)) << ';' << endl;
			} else if( syntax->skips("move") ) {
				Ctxt pctxt = ctxt.parent().value();
				string name = syntax->get_thm_name();
				syntax->skip(':');
				pctxt.claim(name,syntax->get_thm(ctxt));
				syntax->skip(';');
				cout << "theorem " << name << ": " << syntax->pretty_thm(pctxt.thm(name)) << endl;
			} else if( syntax->skips("show") ) {
				string thm_name = syntax->get_thm_name();
				syntax->skip(':');
				Term stmt = syntax->get_term(0).value();
				syntax->skip(';');
				cout << "Proving " << thm_name << ": " << syntax->pretty_term(stmt) << endl;
				auto const& prf = Prover(*this,thm_name,stmt).loop();
				if( !prf.has_value() ) {
					cout << "ERROR: Nothing proved." << endl;
					throw UnfinishedProof();
				}
				Thm const& thm = prf->move(ctxt);
				if( stmt != thm ) {
					cout << "ERROR: Proof mismatch " << syntax->pretty_term(thm) << endl;
					throw UnfinishedProof();
				}
				ctxt.claim(thm_name,thm);
			} else if( syntax->skips("obtain") ) {
				string sym = syntax->get_token();
				syntax->skip("where");
				string spec_name = syntax->get_thm_name();
				syntax->skip(':');
				Term spec = syntax->get_term(0).value();
				syntax->skip(';');
				auto const& pair = ctxt.obtain(sym,spec);
				Term const& goal = pair.first;
				Thm const& obtain_thm = pair.second;
				cout << "Obtaining " << sym << " where " << spec_name << ": " << syntax->pretty_term(spec) << endl <<
					"Proving " << syntax->pretty_term(goal) << endl;
				auto const& prf = Prover(*this,"_obtain_goal",goal).loop();
				if( !prf.has_value() ) {
					cout << "ERROR: Nothing proved." << endl;
					throw UnfinishedProof();
				}
				Thm goal_thm = prf->move(ctxt);
				if( goal != goal_thm ) {
					cout << "ERROR: Proof mismatch " << syntax->pretty_term(goal_thm) << endl;
					throw UnfinishedProof();
				}
				Thm const& spec_thm = obtain_thm.OF(goal_thm);
				ctxt.claim(spec_name,spec_thm);
				cout << "Successfully obtained " << sym << endl;
			} else if( syntax->skips("by") ) {
				if( !thesis.has_value() ) {
					cerr << "No goal for \"by\"" << endl;
					throw UnfinishedProof();
				}
				Thm ret = syntax->get_thm(ctxt);
				syntax->skip(';');
				return ret;
			} else if( syntax->skips("prefix") ) {
				string_view sym = syntax->get_token();
				int rlevel = syntax->get_int();
				int level = syntax->get_int();
				syntax->skips(';');
				_make_own_syntax();
				syntax->prefix(sym,level,rlevel);
				cout << "New prefix operator " << sym << endl;
			} else if( syntax->skips("infix") ) {
				string_view sym = syntax->get_token();
				int llevel = syntax->get_int();
				int rlevel = syntax->get_int();
				int level = syntax->get_int();
				syntax->skips(';');
				_make_own_syntax();
				syntax->infix(sym,level,llevel,rlevel);
				cout << "New infix operator " << sym << endl;
			} else {
				return optional<Thm>();
			}
		} catch ( MalformedDischarge const& e ) {
			cerr << "ERROR: Discharging\n\t" << syntax->pretty_term(e.imp) << endl << "\nwith\t" << syntax->pretty_term(e.arg) << endl;
			throw e;
		} catch ( MalformedInstantiation const& e ) {
			cerr << "ERROR: Instantiating\n\t" << syntax->pretty_term(e.all) << endl << "\nwith\t" << syntax->pretty_term(e.arg) << endl;
			throw e;
		} catch ( TheoremNotFound const& e ) {
			cerr << "ERROR: No thm \"" << e.name << "\" found" << endl;
			throw e;
		}
	}
private:
	void _make_own_syntax() {
		if( !own_syntax ) {
			syntax = Ref(*syntax);
			own_syntax = true;
		}
	}
};

int main(int argc, char* argv[]) {
	istream* pis;
	if( argc == 1 ) {
		pis = &cin;
	} else if( argc == 2 ) {
		pis = new fstream(argv[1]);
	}
	Prover prover = Prover(*pis);
	prover.loop();
	return 0;
}

