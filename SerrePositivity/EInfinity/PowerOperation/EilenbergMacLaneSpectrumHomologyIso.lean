module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSpectrumPiNaturality
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# 全複体上の実 EM スペクトルの整数 π/H 自然同型

DAG XIII §2.2 のスペクトル忘却の比較。元の実 Ω スペクトルの π 関手と、
元の複体のホモロジー関手との自然同型を束ねる。D(A) への降下は別の工程。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (OmegaSpectrum)
variable (A : Type u) [CommRing A]

/-- 元の複体の H^{-j} を乗法記法の可換群として読む関手。 -/
def complexMultiplicativeCohomology (j : ℤ) : Complex A ⥤ CommGrpCat :=
  HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) (-j) ⋙
    forget₂ (ModuleCat A) AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp

/-- 同じ実 EM スペクトルの整数 π/H 比較の全鎖写像に対する自然同型。 -/
def eilenbergMacLaneSpectrumHomologyIso (j : ℤ) :
    eilenbergMacLaneSpectrumFunctor A ⋙ OmegaSpectrum.homotopyFunctor j ≅
      complexMultiplicativeCohomology A j :=
  NatIso.ofComponents
    (fun M => (eilenbergMacLaneSpectrumPiCohomologyEquiv A M j).toCommGrpIso)
    (fun f => by
      ext a
      exact eilenbergMacLaneSpectrumPiCohomologyEquiv_naturality A f j a)

end SerrePositivity.EInfinity.PowerOperation
