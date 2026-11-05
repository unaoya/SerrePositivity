module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityConeComparisonCriterion
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityRightAxisPerfectConeComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityRightAxisLaxDifference
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityConeDiagonalZero
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePerfectYonedaEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.PerfectValuedFunctorExact
public import SerrePositivity.InfinityCategories.Derived.Gluing.Pretriangulated
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeStability
public import SerrePositivity.InfinityCategories.Derived.Gluing.Size
/-!
概要：恒等 Hom gluing の元実 cone 関手を、同じ native lax 比較後の選択 cofiber 差へ全比較する。
方針：実右軸の全同型・対角の指定収縮・小 Perf 像による完全性を局所化判定へ代入する。
規約：元の cone 関手と元の全比較を保持し、全 Perf の Small 性を要求しない。
使われ方：固定入力の恒等 cone 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet DifferentialGraded DGNerve KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants F2.Idempotent
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
  [IsDGPretriangulated R C]
local notation "I" => DGFunctor.id (A := R) C
local notation "M" => dgHomGluingBimodule R C C C I I
local notation "G" => DGGluingObject R C C M
attribute [local irreducible] dgHomGluingBimodule
local instance dgGluingIdentityNativeBase_stable : IsStable (dgNerve R C) := dgNerve_isStable_of_pretriangulated R C
local instance dgGluingIdentityNativeSource_pretriangulated : IsDGPretriangulated R G := dgGluing_isDGPretriangulated R C C M inferInstance inferInstance
local instance dgGluingIdentityNativeSource_stable : IsStable (dgNerve R G) := dgGluingNerve_isStable R C C M inferInstance inferInstance
local instance dgGluingIdentityNativePerfect_stable : IsStable (dgNerve R (PerfectDGModule R C)) := (perfectDGStableModel R C Set.univ).stable

def dgGluingIdentityNativeConeComparison (hC : IsIdempotentComplete (dgNerve R C))
    (z : C) (hz : IsZero (ForgetEnrichment.of (Complex R) z)) : FunctorIso
    (((dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C).hom ≫
      CofiberFamily.cofiber (dgNerve R C)
        (F2.laxPullbackArrow (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C)))) ≫
      (dgGluingNativePerfectYonedaEquivalence R C hC).hom)
    (dgNerve.map (dgHomGluingConeFunctor R C C C I I)) := by
  let B : StableCategory.{u + 1} := ⟨dgNerve R C, inferInstance, inferInstance⟩
  let e := dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C
  let y := dgGluingNativePerfectYonedaEquivalence R C hC
  let f := dgNerve.map (dgHomGluingConeFunctor R C C C I I)
  let i := dgNerve.map (dgGluingIdentityNativeDiagonal.{u, 0} R C)
  let j := dgNerve.map (dgGluingRightAxis R C C M z hz)
  letI : IsExactFunctor f := dgPerfectValuedFunctor_isExactFunctor R G C
    (dgHomGluingConeFunctor R C C C I I)
  have hi : FunctorIso (i ≫ e.hom) (IdentityLax.exactDiagonal B).hom :=
    dgGluingIdentityNativeDiagonalIso.{u, 0} R C
  have hj : FunctorIso ((j ≫ e.hom) ≫ (exactLaxDifference (𝟙 B) (𝟙 B)).hom) (𝟙 B.obj) :=
    dgGluingIdentityRightAxisLaxDifferenceIso R C z hz
  have hf : FunctorIso y.hom (j ≫ f) :=
    F2.functorIsoOfEq (dgGluingIdentityRightAxisPerfectConeIso R C z hz) rfl
      (dgNerve.map_comp _ _)
  have hz' : ∀ x, IsZeroVertex ((i ≫ f).app (Opposite.op ⦋0⦌) x) := by
    intro x
    obtain ⟨x, rfl⟩ := (dgNerve.vertexEquiv R C).symm.surjective x
    change IsZeroVertex ((dgNerve.map (dgHomGluingConeFunctor R C C C I I)).app _
      ((dgNerve.map (dgGluingIdentityNativeDiagonal.{u, 0} R C)).app _ (Simplex.vertex x)))
    erw [dgFunctorNerve_vertex (dgGluingIdentityNativeDiagonal.{u, 0} R C) x,
      dgFunctorNerve_vertex (dgHomGluingConeFunctor R C C C I I)]
    exact dgGluingIdentityConeDiagonal_vertex_zero R C x
  exact identityConeComparisonCriterion B e y f i j hi hj hf hz'

end SerrePositivity.InfinityCategories
