#include "theories.hpp"
#include "syntax.hpp"
#include "syntax.hpp"

using namespace std;

class UnfinishedProof : std::exception {};

class Prover {
	struct Thesis {
		string_view name;
		Ctxt ctxt;
		Term claim;
	};
	Ctxt ctxt;
	bool own_syntax;
	Ref<Syntax> syntax;
	optional<Thesis> thesis;
public:
	Prover() : own_syntax(true) {
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
		thesis({thm_name,parent.ctxt,claim}) {}

	void loop() {
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
				cout << "lemma " << name << ": " << syntax->pretty_thm(ctxt.thm(name)) << endl;
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
				Prover(*this,thm_name,stmt).loop();
			} else if( syntax->skips("by") ) {
				if( !thesis.has_value() ) {
					cerr << "No goal for \"by\"" << endl;
					throw UnfinishedProof();
				}
				auto thm = thesis.value();
				thm.ctxt.claim(thm.name,syntax->get_thm(ctxt));
				syntax->skip(';');
				if( thm.ctxt.thm(thm.name) != thm.claim ) {
					cerr << "ERROR: Proof doesn't match the claim." << endl;
					cerr << "proved " << syntax->pretty_thm(thm.ctxt.thm(thm.name)) << endl;
				} else {
					cerr << "QED" << endl;
				}
				return;
			} else if( syntax->skips("prefix") ) {
				string_view sym = syntax->get_token();
				int level = syntax->get_int();
				int rlevel = syntax->get_int();
				syntax->skips(';');
				_make_own_syntax();
				syntax->prefix(sym,level,rlevel);
				cout << "New prefix operator " << sym << endl;
			} else if( syntax->skips("infix") ) {
				string_view sym = syntax->get_token();
				int level = syntax->get_int();
				int llevel = syntax->get_int();
				int rlevel = syntax->get_int();
				syntax->skips(';');
				_make_own_syntax();
				syntax->infix(sym,level,llevel,rlevel);
				cout << "New infix operator " << sym << endl;
			} else {
				return;
			}
		} catch ( MalformedDischarge const& e ) {
			cerr << "ERROR: Discharging\n\t" << syntax->pretty_term(e.imp) << endl << "\nwith\t" << syntax->pretty_term(e.arg) << endl;
		} catch ( MalformedInstantiation const& e ) {
			cerr << "ERROR: Instantiating\n\t" << syntax->pretty_term(e.all) << endl << "\nwith\t" << syntax->pretty_term(e.arg) << endl;
		} catch ( TheoremNotFound const& e ) {
			cerr << "ERROR: No thm \"" << e.name << "\" found" << endl;
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

int main() {
	Prover obj;
	obj.loop();
	return 0;
}

