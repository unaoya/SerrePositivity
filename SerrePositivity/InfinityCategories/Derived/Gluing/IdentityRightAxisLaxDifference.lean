module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityHomTargetDiagonal
public import SerrePositivity.KST.SConstruction.DGGluingRightAxis
public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroSourceComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGClosedZeroVertex
/-!
概要：恒等 Hom gluing の実右軸上で、選択 lax cofiber 差を元の恒等関手へ全比較する。
方針：元の二射影の厳密回収と実零対象により全矢印族の始域を零と確認する。
規約：同じ native lax 比較と cofiber 選択を保持。使われ方：局所化の試験圏での比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalClosed SSet DifferentialGraded KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
local notation "I" => DGFunctor.id (A := R) C
local notation "M" => dgHomGluingBimodule R C C C I I
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingIdentityHomTargetLaxEquivalence_snd :
    (dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C).hom ≫
      F2.laxPullbackSnd (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C)) =
        dgNerve.map (dgGluingRight R C C M) := by
  change dgGluingIdentityHomTargetLaxComparison.{u, 0} R C ≫ _ = _
  unfold dgGluingIdentityHomTargetLaxComparison
  rw [F2.laxPullbackLift_snd]

variable [IsStable (dgNerve R C)]
  (z : C) (hz : IsZero (ForgetEnrichment.of (Complex R) z))
local notation "J" => dgGluingRightAxis R C C M z hz

def dgGluingIdentityRightAxisLaxDifferenceIso : FunctorIso
    ((dgNerve.map J ≫ (dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C).hom) ≫
      CofiberFamily.cofiber (dgNerve R C)
        (F2.laxPullbackArrow (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C))))
    (𝟙 (dgNerve R C)) := by
  let j := dgNerve.map J ≫ (dgGluingIdentityHomTargetLaxEquivalence.{u, 0} R C).hom
  let a := j ≫ F2.laxPullbackArrow (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C))
  have h₀ : a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      dgNerve.map (dgClosedZeroFunctor R z hz C) := by
    simp only [a, j, Category.assoc, F2.laxPullbackArrow_source, Category.comp_id,
      dgGluingIdentityHomTargetLaxEquivalence_fst]
    rw [← dgNerve.map_comp, dgGluingRightAxis_left]
  have h₁ : a ≫ ArrowTarget.target (dgNerve R C) = 𝟙 _ := by
    change a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
    simp only [a, j, Category.assoc, F2.laxPullbackArrow_target, Category.comp_id,
      dgGluingIdentityHomTargetLaxEquivalence_snd]
    rw [← dgNerve.map_comp, dgGluingRightAxis_right, dgNerve.map_id]
  have ha : ∀ x, IsZeroSourceArrow (a.app (Opposite.op ⦋0⦌) x) := by
    intro x
    change IsZeroVertex ((a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _ x)
    rw [h₀]
    obtain ⟨x, rfl⟩ := (dgNerve.vertexEquiv R C).symm.surjective x
    erw [dgGluingIdentityNerveMap_vertex.{u, 0} R C]
    exact dgNerve_isZeroVertex_of_closed_isZero z hz
  have h := (CofiberFamily.precompositionIso
    (F2.laxPullbackArrow (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C))) j).trans
      (cofiberZeroSourceIso (dgNerve R C) a ha)
  exact F2.functorIsoOfEq h rfl h₁

end SerrePositivity.InfinityCategories
