import SSU.Engines.LargeSieve.AdditiveMV
import SSU.Engines.LargeSieve.DualSieveFromInterzoneZ
import SSU.Engines.LargeSieve.MVExponentialGram
import SSU.Engines.LargeSieve.MVFiniteLargeSieveZ
import SSU.Engines.LargeSieve.MVFiniteLargeSieveZInterface

/-!
Large sieve (Montgomery–Vaughan) engine layer: basic lemmas.

This is a small import hub for the analytic starter lemmas:
* `AdditiveMV` (Dirichlet kernel / geometric-sum bounds),
* `DualSieveFromInterzoneZ` (row-sum Gram bound ⇒ dual large sieve inequality).

The actual Step 3/4 SSU bounds (TeX `05b_SSU.tex`) are wired in
`SSU.Engines.LargeSieve.MontgomeryVaughanTypeII`.
-/
