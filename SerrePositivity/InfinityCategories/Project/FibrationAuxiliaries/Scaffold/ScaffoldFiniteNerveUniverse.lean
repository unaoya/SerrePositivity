module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldNerveFirstEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LocalKanDiagramStrictification

/-!
概要：大きい有限鎖の nerve と元の小さい nerve の宇宙持ち上げを同じ頂点で結ぶ。
方針：標準単体を経由し、最初の辺・尾部・零頂点への自然性を各頂点で確認する。
規約：元の全有限鎖とその包含を保持する。
使われ方：高次単体の source と分類先の Segal 表示の宇宙を揃える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold

/-- 大きい有限鎖を、小さい同じ有限鎖の nerve の持ち上げと同一視する。 -/
def scaffoldFiniteNerveUniverseIso (n : ℕ) :
    nerve (ULift.{u + 1} (Fin (n + 1))) ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin (n + 1)))) :=
  (stdSimplex.isoNerve.{u + 1} n).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} n

/-- 同じ宇宙比較を標準単体から読むと、元の底の表示同型そのもの。 -/
lemma scaffoldFiniteNerveUniverseIso_std (n : ℕ) :
    (stdSimplex.isoNerve.{u + 1} n).hom ≫ (scaffoldFiniteNerveUniverseIso.{u} n).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} n).hom := by
  simp only [scaffoldFiniteNerveUniverseIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

/-- 宇宙表示の比較は元の最初の辺の包含と厳密に可換。 -/
lemma scaffoldFiniteNerveUniverseIso_first (n : ℕ) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge.{u + 1} n) ≫
        (scaffoldFiniteNerveUniverseIso.{u} (n + 1)).hom =
      (scaffoldFiniteNerveUniverseIso.{u} 1).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge.{u} n)) := by
  ext d s
  apply ULift.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 宇宙表示の比較は元の尾部の包含と厳密に可換。 -/
lemma scaffoldFiniteNerveUniverseIso_tail (n : ℕ) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail.{u + 1} n) ≫
        (scaffoldFiniteNerveUniverseIso.{u} (n + 1)).hom =
      (scaffoldFiniteNerveUniverseIso.{u} n).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail.{u} n)) := by
  ext d s
  apply ULift.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 有限鎖の同じ零頂点を、一点圏からの通常関手として表示する。 -/
def scaffoldFiniteZeroVertex (n : ℕ) :
    ULift.{u} (Fin 1) ⥤ ULift.{u} (Fin (n + 1)) :=
  (CategoryTheory.Functor.const _).obj (ULift.up 0)

/-- 同じ零頂点の包含も、標準零単体の宇宙表示と厳密に可換。 -/
lemma scaffoldFiniteNerveUniverseIso_point (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u + 1} _) ≫
        (scaffoldFiniteNerveUniverseIso.{u} n).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 0).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (scaffoldFiniteZeroVertex.{u} n)) := by
  ext d s
  apply ULift.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold
