module

public import SerrePositivity.EInfinity.PowerOperation.CyclicOrbitFiniteSum
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# 同じ orbit 直和全複体の有限座標

DAG XIII Construction 2.2.6 の正の周期 Hom 比較の補助。
零延長・零支持の除去・添字の同値・正則余不変の指定評価を合成する。
このファイルは各次数の実同型までを扱い、鎖同型とはまだ主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 整数の非負添字で、同じ零延長の項を正則係数へ戻す。 -/
def cyclicOrbitResolutionXIsoInt (s : ℤ) (hs : 0 ≤ s) :
    (cyclicOrbitResolution p k).X (-s) ≅
      Rep.leftRegular k (PowerOperationCyclicGroup.{u} p) :=
  (cyclicOrbitProjectiveResolution p k).complex.extendXIso
    ComplexShape.embeddingDownNat (i := s.toNat)
      (show ComplexShape.embeddingDownNat.f s.toNat = -s by
        simp [ComplexShape.embeddingDownNat, Int.toNat_of_nonneg hs])

variable (M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ)
    (d : ℤ) [M.IsStrictlyLE d] (n : ℤ)

/-- 同じ有限な対角成分を、同じ正則評価で係数加群へ移す。 -/
def cyclicOrbitFiniteSummandIso (s : {s : ℤ // s ∈ Finset.Icc 0 (d - n)}) :
    cyclicOrbitDiagonalSummand p k M n
        ((cyclicOrbitFiniteDiagonalEquiv d n).symm s).1 ≅
      ModuleCat.of k (M.X (s.1 + n)) :=
  ((Rep.coinvariantsTensor k (PowerOperationCyclicGroup.{u} p)).obj
    (M.X (s.1 + n))).mapIso
      (cyclicOrbitResolutionXIsoInt p k s.1 (Finset.mem_Icc.mp s.2).1) ≪≫
    (regularOrbitEvaluation (M.X (s.1 + n))).toModuleIso

/-- 元の直和全複体の項と、係数の有限な積の指定実同型。 -/
def cyclicOrbitTotalDegreeCoordinatesIso :
    ((cyclicOrbitTotalFunctor p k).obj M).X n ≅
      ModuleCat.of k (∀ s : {s : ℤ // s ∈ Finset.Icc 0 (d - n)}, M.X (s.1 + n)) :=
  cyclicOrbitTotalDegreeFiniteSumIso p k M d n ≪≫
    Sigma.mapIso (cyclicOrbitFiniteSummandIso p k M d n) ≪≫
    (biproduct.isoCoproduct
      (fun s : {s : ℤ // s ∈ Finset.Icc 0 (d - n)} =>
        ModuleCat.of k (M.X (s.1 + n)))).symm ≪≫
    ModuleCat.biproductIsoPi _

end SerrePositivity.EInfinity.PowerOperation
