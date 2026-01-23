-- All.lean
import Twin.Final
import Twin.Gold
import Goldbach.TwinGold
import Goldbach.ETIExport

-- Main track toggles
-- import Goldbach.Final
-- import Goldbach.Complete

-- Tenor-aligned closure track (staging; compiles, but not yet connected to analytics)
-- import Goldbach.ClosureBridgeTenor
-- import Goldbach.FinalTenor
-- import Goldbach.CompleteTenor

-- Canonical Goldbach track (Tenor-aligned parallel FunX), *gold-grade boundary*.
import Goldbach.GoldFunX_OptionB_Gold

-- Optional: pinned-cap turnkey route (fool's gold; import explicitly if desired).
-- import Goldbach.GoldFunX_OptionB_Cert

-- Offline/turnkey major-arc staging area (kept modular, but built in CI).
import Goldbach.Cert.MajorArcModules.All

-- Optional: conditional entry points (kept for reference).
-- import Goldbach.CompleteFun
-- import Goldbach.CompleteTenorFunX
