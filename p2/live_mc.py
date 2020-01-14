import pynusmv
import sys

def reacheability(fsm):
    reach = fsm.init
    new = fsm.init
    while fsm.count_states(new) != 0 :
        new = fsm.post(new) - reach
        reach = reach + new
    return reach

def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def check_persistently(spec):
    """
    Return whether the property `spec` is persistent or not in the loaded SMV model, 
    that is, whether all traces of the model satisfies the LTL formula `F G spec` or not. 

    The result is a boolean telling whether `spec` is persistent.
    """
    fsm = pynusmv.glob.prop_database().master.bddFsm
    spec = spec_to_bdd(fsm,spec)
    return not RSA(~spec)

def check_repeatedly(spec):
    """
    Return whether the property `spec` is recurrent or not in the loaded SMV model, 
    that is, whether all traces of the model satisfies the LTL formula `G F spec` or not.

    The result is a boolean telling whether `spec` is recurrent or not.
    """
    fsm = pynusmv.glob.prop_database().master.bddFsm
    spec = spec_to_bdd(fsm,spec)
    return not PSA(~spec)
  
def RSA(spec):
    
    fsm = pynusmv.glob.prop_database().master.bddFsm
    reach = reacheability(fsm)
    recur = reach * spec
    while (fsm.count_states(recur) != 0):
        reach = pynusmv.dd.BDD.false()
        new = fsm.pre(recur)
        while (fsm.count_states(new) != 0):
            reach = reach + new 
            if ( recur * reach == recur ):
                return True
            new = fsm.pre(new) - reach
        recur = recur * reach
    return False

def PSA(spec):
    
    fsm = pynusmv.glob.prop_database().master.bddFsm
    reach = reacheability(fsm)
    recur = reach * spec
    while (fsm.count_states(recur) != 0):
        reach = pynusmv.dd.BDD.false()
        new = fsm.pre(recur) * spec
        while (fsm.count_states(new) != 0):
            reach = reach + new 
            if ( recur * reach == recur ):  #recur == reach
                return True
            new = (fsm.pre(new)*spec) - reach
        recur = recur * reach
    return False

if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    if prop.type == invtype :
        print("Property", spec, "is an INVSPEC.")
        res = check_persistently(spec)
        if res == True:
            print("Property is persistent")
        else:
            print("Property is not persistent")
        res = check_repeatedly(spec)
        if res == True:
            print("Property is recurrent")
        else:
            print("Property is not recurrent")
    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()
