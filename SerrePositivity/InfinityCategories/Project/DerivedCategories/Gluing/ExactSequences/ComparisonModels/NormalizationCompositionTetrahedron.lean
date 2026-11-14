module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.NormalizationTetrahedronFilling
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.NormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.DGCompositionTriangleFamily

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)

/-- 概要：元 Hom と終標準閉射の実合成三角形。
方針：同じ二入力の標準 dg nerve 三角形を使う。
規約：前正規化前の Hom を保持する。使われ方：四面体の第零面。 -/
def dgGluingNormalizationExitTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R Q f
    (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R Q
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y)))

lemma dgGluingNormalizationCompositionTetrahedron_exists :
    ∃ V : (Δ[3] : SSet.{max u v}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Q,
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ V = dgGluingNormalizationExitTriangle R E X Y f ∧
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ V =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizePrism R E X Y f) ∧
      (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ V =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizePrism R E X Y f) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTetrahedronFamily_exists
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_front, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizePrism_projection,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_one, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizePrism_zero,
      ← Category.assoc f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedSliceEvaluation]
  · rw [dgGluingNormalizationExitTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_two,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizePrism_one,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedSliceEvaluation]
  · rw [dgGluingNormalizationExitTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_zero,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizePrism_one,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedSliceEvaluation]

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
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizePrism R E X Y f) :=
  (Classical.choose_spec (dgGluingNormalizationCompositionTetrahedron_exists R E X Y f)).2.1

lemma dgGluingNormalizationCompositionTetrahedron_three :
    (stdSimplex.δ (3 : Fin 4) ▷ K) ≫
        dgGluingNormalizationCompositionTetrahedron R E X Y f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizePrism R E X Y f) :=
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
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizePrism R E X Y f) := by
  have he : stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
      stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) :=
    stdSimplex.δ_comp_δ (i := (1 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  rw [dgGluingNormalizationEntranceTriangle, ← Category.assoc, ← comp_whiskerRight,
    he, comp_whiskerRight, Category.assoc, dgGluingNormalizationCompositionTetrahedron_one]

lemma dgGluingNormalizationEntranceTriangle_two :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ dgGluingNormalizationEntranceTriangle R E X Y f =
      (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizePrism R E X Y f) := by
  have he : stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
      stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) :=
    (stdSimplex.δ_comp_δ (i := (2 : Fin 3)) (j := (2 : Fin 3)) (by decide)).symm
  rw [dgGluingNormalizationEntranceTriangle, ← Category.assoc, ← comp_whiskerRight,
    he, comp_whiskerRight, Category.assoc, dgGluingNormalizationCompositionTetrahedron_three]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
