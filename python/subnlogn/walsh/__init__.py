"""The Walsh-route middle transform (M9; SPEC_WALSH, a delta on SPEC).

* :mod:`subnlogn.walsh.gadget`     -- selective Walsh operation and exact CNOT batches (SPEC_WALSH §2-§3).
* :mod:`subnlogn.walsh.positional` -- slices, two-involution positional maps, layout compile (§4).
* :mod:`subnlogn.walsh.fft`        -- last-axis FFT, direct complex tensor FFT, bridge backend "walsh" (§5-§6).
"""

from .gadget import WalshCtx, cnot_batch, selective_walsh  # noqa: F401
