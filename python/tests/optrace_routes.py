"""The routes and hierarchy stages run by the operator-level guard (tests/optrace_run.py, imported there after the
tracer is installed, so its schedules come from the traced copy) and by tests/test_optrace_guard.py (untraced: the
exact expected stub calls of each route).  Not part of the library."""

from subnlogn.schedule import faithful_schedule, test_policy, test_schedule

ROUTES = {
    # name: (schedule factory, n bits)
    "faithful2d": (faithful_schedule, 600),
    "deep2d": (lambda: test_schedule(base_threshold=2), 160),
    "bluestein": (lambda: test_policy(2, middle="bluestein"), 96),
    "walsh": (lambda: test_policy(2, middle="walsh"), 96),
    "direct": (lambda: test_policy(2, middle="direct"), 96),
    "network": (lambda: test_policy(4, middle="bluestein"), 96),
    "walsh_network": (lambda: test_policy(4, middle="walsh"), 96),
    "faithful2d_big": (faithful_schedule, 6000),
}
#: stage routes: (Hierarchy method, operand bits, Hierarchy kwargs) -- the stages in isolation
STAGES = {
    "multiply1": ("multiply1", 3000, lambda: {}),
    "multiply2": ("multiply2", 400, lambda: {"stage_schedule": test_schedule(base_threshold=2)}),
    "basic": ("basic_mul", 2000, lambda: {}),
}
