import pynusmv
import sys
sys.setrecursionlimit(10**6)

def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec


def reacheability(phi):
    reach = fsm.init
    new = fsm.init
    while new.size != 0 :
        if new*spec.size !=0 : return True # set of stast that satisfies spec
        #else
        new = fsm.post(new) - reach
        reach = reach + new
    return False

def check_explain_inv_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the invariant
    `spec`, that is, whether all reachable states of the model satisfies `spec`
    or not. Return also an explanation for why the model does not satisfy
    `spec``, if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `spec`
    otherwise.

    The explanation is a tuple of alternating states and inputs, starting
    and ennding with a state. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    fsm = pynusmv.glob.prop_database().master.bddFsm
    spec = spec_to_bdd(fsm,spec)
    ############
    reach = fsm.init 
    new = fsm.init
    n = fsm.count_states(reach)

    found_unhappy_state = False
    counterexample = None

    while fsm.count_states(new)>0 & found_unhappy_state==False:

        unhappy_states = new*(~spec)

        if fsm.count_states(unhappy_states)>0 : #spec non vale in tutti gli stati
            found_unhappy_state = True
            unhappy_state = fsm.pick_one_state(unhappy_states)
            counterexample = path_to(fsm,reach,unhappy_state)

        new = fsm.post(new) - reach
        fsm.pre
        reach = reach + new 

    return (not found_unhappy_state,counterexample)

def path_to(fsm, reach, state_bdd):
    
    #if state_bdd == None or fsm.count_states(state_bdd)==0: return []
    i = fsm.count_states(state_bdd * fsm.init)
    if i>0 : 
        return [state_bdd.get_str_values()]
    pred = fsm.pick_one_state(fsm.pre(state_bdd)*reach)
    return path_to(fsm,reach,pred)+[state_bdd.get_str_values()]


if len(sys.argv) != 2:
    # print("Usage:", sys.argv[0], "filename.smv")
    # sys.exit(1)
    filename="railroad_wrong.smv"
else:
       filename = sys.argv[1] 

pynusmv.init.init_nusmv()

pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    if prop.type == invtype:
        print("Property", spec, "is an INVARSPEC.")
        res, trace = check_explain_inv_spec(spec)
        if res == True:
            print("Invariant is respected")
        else:
            print("Invariant is not respected")
            print(trace)
    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()
