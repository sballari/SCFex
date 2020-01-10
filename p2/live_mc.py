import pynusmv
import sys

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
    ltlspec = pynusmv.prop.f(pynusmv.prop.g(spec))
    res = pynusmv.mc.check_ltl_spec(ltlspec)
    return res

def check_repeatedly(spec):
    """
    Return whether the property `spec` is recurrent or not in the loaded SMV model, 
    that is, whether all traces of the model satisfies the LTL formula `G F spec` or not.

    The result is a boolean telling whether `spec` is recurrent or not.
    """
    ltlspec = pynusmv.prop.g(pynusmv.prop.f(spec))
    res = pynusmv.mc.check_ltl_spec(ltlspec)
    return res


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
    if prop.type == invtype:
        print("Property", spec, "is an INVARSPEC.")
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
