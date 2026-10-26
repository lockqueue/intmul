"""M3: the Bluestein middle tensor DFT with direct (non-network) layers.

* :mod:`.layout`    -- Lemma 16 layout L (prefix moves + chunk exchanges) as a slot descriptor.
* :mod:`.synth`     -- Lemma 16 synthetic transforms L·B·F_t^- and F_t^+·B^-1·L^-1 over R_r.
* :mod:`.prop18`    -- Proposition 18 normalized ring convolution (Lemma 17 products).
* :mod:`.bluestein` -- coefficient twist (Pr §9.4), positive tensor DFT by the chirp identity
  (Lemma 21 (36), §9.5), registered as the bridge middle backend ``"bluestein"``.

Source: SPEC §5 (authoritative), the preprint [OAI26].
"""
