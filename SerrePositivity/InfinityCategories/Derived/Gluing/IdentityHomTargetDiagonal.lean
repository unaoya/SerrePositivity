module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityHomTargetLaxEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaObject
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxComparisonVertexImage
public import SerrePositivity.KST.SConstruction.DGHomGluingStrictSquare
public import SerrePositivity.KST.LocalizingInvariants.EquivalenceArrowFamily
public import SerrePositivity.KST.LocalizingInvariants.ArrowStableExact
/-!
概要：恒等 Hom gluing の実対角を、同じ全比較を通して恒等矢印の対角へ比較する。
方針：指定 augmentation の各頂点の恒等辺を確認し、可逆矢印の全族を始点の恒等族へ移す。
規約：対象別同型で代用しない。使われ方：恒等二脚の対角欄の全比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet DifferentialGraded DGNerve KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
local notation "I" => DGFunctor.id (A := R) C
local notation "M" => dgHomGluingBimodule R C C C I I
local notation "G" => DGGluingObject R C C M

def dgGluingIdentityNativeDiagonal : DGFunctor R C G :=
  dgStrictSquareDiagonal R C C C I I I I rfl

lemma dgGluingIdentityNativeDiagonal_targetMap (x : C) :
    dgHomGluingTargetMap R C C C I I ((dgGluingIdentityNativeDiagonal R C).obj x) =
      𝟙 (ForgetEnrichment.of (Complex R) x) := by
  exact dgHomGluingTargetMap_comparisonObject R C C C I I I I
    (fun y => 𝟙 (ForgetEnrichment.of (Complex R) y)) x

attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingIdentityHomTargetLaxEquivalence_fst :
    (dgGluingIdentityHomTargetLaxEquivalence.{u, v} R C).hom ≫
      F2.laxPullbackFst (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C)) =
        dgNerve.map (dgGluingLeft R C C M) := by
  change dgGluingIdentityHomTargetLaxComparison.{u, v} R C ≫ _ = _
  unfold dgGluingIdentityHomTargetLaxComparison
  rw [F2.laxPullbackLift_fst]

lemma dgGluingIdentityHomTargetLaxEquivalence_arrow :
    (dgGluingIdentityHomTargetLaxEquivalence.{u, v} R C).hom ≫
      F2.laxPullbackArrow (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C)) =
        dgGluingHomTargetAugmentationArrowFamily R C C C I I := by
  change dgGluingIdentityHomTargetLaxComparison.{u, v} R C ≫ _ = _
  unfold dgGluingIdentityHomTargetLaxComparison
  rw [F2.laxPullbackLift_arrow]

lemma dgGluingIdentityDiagonal_lax_fst :
    (dgNerve.map (dgGluingIdentityNativeDiagonal R C) ≫
      (dgGluingIdentityHomTargetLaxEquivalence.{u, v} R C).hom) ≫
        F2.laxPullbackFst (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C)) = 𝟙 _ := by
  rw [Category.assoc, dgGluingIdentityHomTargetLaxEquivalence_fst, ← dgNerve.map_comp]
  unfold dgGluingIdentityNativeDiagonal
  rw [dgStrictSquareDiagonal_left, dgNerve.map_id]

lemma dgGluingIdentityNerveMap_vertex {D : Type (max (u + 1) v)} [DGCategory R D]
    (F : DGFunctor R C D) (x : C) :
    (dgNerve.map F).app (Opposite.op ⦋0⦌) (Simplex.vertex x) = Simplex.vertex (F.obj x) := by
  apply (Simplex.vertexEquiv (A := R) (D := D)).injective
  rfl

lemma dgGluingIdentityAugmentation_vertex (X : G) :
    intervalFunctorVertexEdge
      ((dgGluingHomTargetAugmentationArrowFamily R C C C I I).app (Opposite.op ⦋0⦌)
        (Simplex.vertex X)) = (dgClosedEdge R C (dgHomGluingTargetMap R C C C I I X)).edge := by
  unfold dgGluingHomTargetAugmentationArrowFamily
  rw [dgGluingCurryHomotopy_vertex_edge, dgGluingHomTargetAugmentationHomotopy_vertex_edge]

attribute [local irreducible] dgGluingHomTargetAugmentationArrowFamily

lemma dgGluingIdentityDiagonal_arrow_vertex (x : (dgNerve R C) _⦋0⦌) :
    IsEquivalencePathVertex
      ((dgNerve.map (dgGluingIdentityNativeDiagonal R C) ≫
        (dgGluingIdentityHomTargetLaxEquivalence.{u, v} R C).hom ≫
          F2.laxPullbackArrow (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C))).app
            (Opposite.op ⦋0⦌) x) := by
  obtain ⟨x, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := C)).symm.surjective x
  rw [dgGluingIdentityHomTargetLaxEquivalence_arrow]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  erw [dgGluingIdentityNerveMap_vertex]
  unfold IsEquivalencePathVertex
  erw [dgGluingIdentityAugmentation_vertex,
    dgGluingIdentityNativeDiagonal_targetMap, dgGluingClosedIdentityEdge R C x]
  have h := isEquivalencePathVertex_const (Y := dgNerve R C) (Simplex.vertex (A := R) x)
  unfold IsEquivalencePathVertex at h
  rw [intervalFunctorVertexEdge_functorVertex] at h
  exact h

def dgGluingIdentityNativeDiagonalIso : FunctorIso
    (dgNerve.map (dgGluingIdentityNativeDiagonal R C) ≫
      (dgGluingIdentityHomTargetLaxEquivalence.{u, v} R C).hom)
    (constantFunctorMap (Δ[1] : SSet) (dgNerve R C) ≫ arrowLaxInverse (dgNerve R C)) := by
  let f := dgNerve.map (dgGluingIdentityNativeDiagonal R C) ≫
    (dgGluingIdentityHomTargetLaxEquivalence.{u, v} R C).hom
  let a := f ≫ F2.laxPullbackArrow (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C))
  have ha : ∀ x, IsEquivalencePathVertex (a.app (Opposite.op ⦋0⦌) x) :=
    dgGluingIdentityDiagonal_arrow_vertex R C
  have e := (EquivalenceArrowFamily.comparison a ha).postcomp (arrowLaxInverse (dgNerve R C))
  have hs : a ≫ arrowLaxInverse (dgNerve R C) = f := by
    change (f ≫ (arrowLaxIso (dgNerve R C)).hom) ≫ (arrowLaxIso (dgNerve R C)).inv = f
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ht : a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = 𝟙 _ := by
    rw [show a = f ≫ F2.laxPullbackArrow (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C)) from rfl,
      Category.assoc, F2.laxPullbackArrow_source, Category.comp_id]
    exact dgGluingIdentityDiagonal_lax_fst R C
  rw [hs, ht, Category.id_comp] at e
  exact e

end SerrePositivity.InfinityCategories
