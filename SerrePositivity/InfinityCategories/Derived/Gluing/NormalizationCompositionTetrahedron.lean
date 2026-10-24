module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationTetrahedronFilling
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTriangleFamily

/-! # 前後正規化と終側合成を保つ実四面体

概要：元 Hom の前後正規化を、一つの四面体の三つの指定面として保持する。
方針：終側の標準合成三角形と前後の二三角形を内角へ貼って充填する。
規約：指定面・全入力は変えず、第四面だけを選ぶ。Small 仮定は導入しない。
使われ方：augmentation の側面も含む相対二次元比較の基礎となる合成整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)

/-- 概要：元 Hom と終標準閉射の実合成三角形。
方針：同じ二入力の標準 dg nerve 三角形を使う。
規約：前正規化前の Hom を保持する。使われ方：四面体の第零面。 -/
def dgGluingNormalizationExitTriangle :=
  dgGluingDGCompositionTriangleFamily R Q f
    (SSet.const (X := K) (pinchedClosedVertex R Q
      (dgGluingIdentityCommaNormalizationClosedOut R E Y)))

lemma dgGluingNormalizationCompositionTetrahedron_exists :
    ∃ V : (Δ[3] : SSet.{max u v}) ⊗ K ⟶ dgNerve R Q,
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ V = dgGluingNormalizationExitTriangle R E X Y f ∧
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ V =
        dgGluingSlicePrismTriangle (dgGluingIdentityCommaPostNormalizePrism R E X Y f) ∧
      (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ V =
        dgGluingSlicePrismTriangle (dgGluingIdentityCommaPreNormalizePrism R E X Y f) := by
  apply dgGluingTetrahedronFamily_exists
  · rw [dgGluingSlicePrismTriangle_front, dgGluingIdentityCommaPostNormalizePrism_projection,
      dgGluingSlicePrismTriangle_one, dgGluingIdentityCommaPreNormalizePrism_zero,
      ← Category.assoc f, dgGluingPinchedSliceEvaluation]
  · rw [dgGluingNormalizationExitTriangle, dgGluingDGCompositionTriangleFamily_two,
      dgGluingSlicePrismTriangle_zero, dgGluingIdentityCommaPreNormalizePrism_one,
      dgGluingPinchedSliceEvaluation]
  · rw [dgGluingNormalizationExitTriangle, dgGluingDGCompositionTriangleFamily_zero,
      dgGluingSlicePrismTriangle_zero, dgGluingIdentityCommaPostNormalizePrism_one,
      dgGluingPinchedSliceEvaluation]

/-- 概要：前後と終側の三つの実標準面を保つ四面体。
方針：全パラメーターの内角充填を選ぶ。
規約：充填は公開する三面を厳密に回収する。使われ方：側面を含む貼り合わせ。 -/
def dgGluingNormalizationCompositionTetrahedron :=
  Classical.choose (dgGluingNormalizationCompositionTetrahedron_exists R E X Y f)

lemma dgGluingNormalizationCompositionTetrahedron_zero :
    (stdSimplex.δ (0 : Fin 4) ▷ K) ≫
        dgGluingNormalizationCompositionTetrahedron R E X Y f =
      dgGluingNormalizationExitTriangle R E X Y f :=
  (Classical.choose_spec (dgGluingNormalizationCompositionTetrahedron_exists R E X Y f)).1

lemma dgGluingNormalizationCompositionTetrahedron_one :
    (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
        dgGluingNormalizationCompositionTetrahedron R E X Y f =
      dgGluingSlicePrismTriangle (dgGluingIdentityCommaPostNormalizePrism R E X Y f) :=
  (Classical.choose_spec (dgGluingNormalizationCompositionTetrahedron_exists R E X Y f)).2.1

lemma dgGluingNormalizationCompositionTetrahedron_three :
    (stdSimplex.δ (3 : Fin 4) ▷ K) ≫
        dgGluingNormalizationCompositionTetrahedron R E X Y f =
      dgGluingSlicePrismTriangle (dgGluingIdentityCommaPreNormalizePrism R E X Y f) :=
  (Classical.choose_spec (dgGluingNormalizationCompositionTetrahedron_exists R E X Y f)).2.2

/-- 概要：正規化の四面体から残る始側の合成面を得る。
方針：第二面へ制限する。規約：他三面を変えない。
使われ方：共有対角と元の始辺を両立させる相対比較。 -/
def dgGluingNormalizationEntranceTriangle :=
  (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ dgGluingNormalizationCompositionTetrahedron R E X Y f

lemma dgGluingNormalizationEntranceTriangle_zero :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ dgGluingNormalizationEntranceTriangle R E X Y f =
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ dgGluingNormalizationExitTriangle R E X Y f := by
  have he : stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
      stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) :=
    stdSimplex.δ_comp_δ (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  rw [dgGluingNormalizationEntranceTriangle, ← Category.assoc, ← comp_whiskerRight,
    he, comp_whiskerRight, Category.assoc, dgGluingNormalizationCompositionTetrahedron_zero]

lemma dgGluingNormalizationEntranceTriangle_one :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ dgGluingNormalizationEntranceTriangle R E X Y f =
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫
        dgGluingSlicePrismTriangle (dgGluingIdentityCommaPostNormalizePrism R E X Y f) := by
  have he : stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
      stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) :=
    stdSimplex.δ_comp_δ (i := (1 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  rw [dgGluingNormalizationEntranceTriangle, ← Category.assoc, ← comp_whiskerRight,
    he, comp_whiskerRight, Category.assoc, dgGluingNormalizationCompositionTetrahedron_one]

lemma dgGluingNormalizationEntranceTriangle_two :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ dgGluingNormalizationEntranceTriangle R E X Y f =
      (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
        dgGluingSlicePrismTriangle (dgGluingIdentityCommaPreNormalizePrism R E X Y f) := by
  have he : stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
      stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) :=
    (stdSimplex.δ_comp_δ (i := (2 : Fin 3)) (j := (2 : Fin 3)) (by decide)).symm
  rw [dgGluingNormalizationEntranceTriangle, ← Category.assoc, ← comp_whiskerRight,
    he, comp_whiskerRight, Category.assoc, dgGluingNormalizationCompositionTetrahedron_three]

end SerrePositivity.InfinityCategories
