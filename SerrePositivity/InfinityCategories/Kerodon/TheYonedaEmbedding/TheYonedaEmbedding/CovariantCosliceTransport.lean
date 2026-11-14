module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CovariantCosliceClassification
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCoslicePostIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.UniversePointCoslice

/-!
概要：大きい底の表示上で作った表現可能な全空間比較を、小さい底の分類へ戻す。
方針：底の同型、全 coslice の宇宙同型、unstraightening の引き戻しを合成する。
規約：比較射の底は厳密に保持する。
使われ方：対象宇宙だけを持ち上げた単体的圏から元の共変 Hom 図式への帰還。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 底の同型で表示した coslice の全空間同値から、元の小さい底上の全図式同型を得る。 -/
def covariantHomIsoOfDisplayedCosliceEquivalence
    {B : SSet.{u}} [Quasicategory B] {C : SSet.{u + 1}} [Quasicategory C]
    (e : C ≅ (SSet.uliftFunctor.{u + 1, u}).obj B)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (G : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hg : e.hom ≫ F = G)
    (x : C _⦋0⦌) (b : B _⦋0⦌) (hb : e.hom.app (Opposite.op ⦋0⦌) x = ULift.up b)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening G)
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x))
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant b) := by
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCoslicePostIso e x ≪≫
    eqToIso (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm z)) hb)
  have ha : a.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{u + 1, u}).obj B)).symm (ULift.up b)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x) ≫ e.hom := by
    dsimp only [a, Iso.trans_hom, eqToIso.hom]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnder_eqToHom_projection
      (congrArg SSet.yonedaEquiv.symm hb)]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCoslicePostIso_projection e x
  have hai : a.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x) ≫ e.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
        ((SSet.yonedaEquiv (X := (SSet.uliftFunctor.{u + 1, u}).obj B)).symm (ULift.up b)) := by
    rw [← ha, ← Category.assoc, a.inv_hom_id, Category.id_comp]
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap G F e.hom hg
  have gi : IsIso g := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_isPullback G F e.hom hg).isIso_fst_of_isIso
  let k := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointCosliceUniverseIso.{u, u + 1} b).hom ≫ a.inv ≫ f ≫ g
  have kp : k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b)) := by
    dsimp only [k, g]
    rw [Category.assoc, Category.assoc, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_projection, ← Category.assoc f, hf,
      hai, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointCosliceUniverseIso_projection]
  have ke : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence k :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointCosliceUniverseIso.{u, u + 1} b)).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso a.symm).comp
        (he.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso g))))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantHomIsoOfCosliceEquivalence F b k kp ke

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
