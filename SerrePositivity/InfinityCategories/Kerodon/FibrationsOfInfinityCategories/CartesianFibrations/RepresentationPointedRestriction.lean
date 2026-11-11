module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationComparisonRestriction

/-!
概要：cartesian な比較の全空間側の作用と pointed な射の前合成を同定する。
方針：表現空間の pointed 射影の可換式を頂点同型の像へ移す。
規約：分類図式の比較と同じ頂点同型を使う。
使われ方：余単位の自然性と全空間比較を同時に保持する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：表現空間の cartesian 制限は pointed な射の前合成と可換。
方針：全部分複体の包含後に四角形空間の射影公式を使う。
規約：全高次パラメーターでの等式。
使われ方：全空間側の同型の自然性。 -/
lemma transportWitnessPre_pointed {p q : Arrow SSet.{u + 1}}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPointed p.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPointed q.hom ≫ (pre f.left).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPointed, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre_ι,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquarePre_pointed]
  rfl

/-- 概要：cartesian 制限の pointed な比較は元の比較の全空間の射での前合成。
方針：図式側と同じ表現の比較を pointed な射影へ写す。
規約：制限の pointed な射の一致による端点の移送を明示する。
使われ方：図式側と全空間側を同時に保つ自然性の界面。 -/
lemma LeftTransportRepresentation.cartesianRestrict_pointedIso
    {E F B D : SSet.{u + 1}} {p : E ⟶ B} {q : F ⟶ D}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (R S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex S))
    (e : F ⟶ E) (g : D ⟶ B) (h : IsPullback e q p g) :
    (R.cartesianRestrict e g h).pointedIso (S.cartesianRestrict e g h)
      (R.cartesianRestrictVertexIso S a e g h) =
      eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d))
        (R.cartesianRestrict_pointedMap e g h)) ≪≫ (R.pointedIso S a).precomp e ≪≫
      (eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d))
        (S.cartesianRestrict_pointedMap e g h))).symm := by
  let f : Arrow.mk q ⟶ Arrow.mk p := Arrow.homMk e g h.w
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (Arrow.mk q).hom := by change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q; infer_instance
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (Arrow.mk p).hom := by change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p; infer_instance
  have hd := transportWitnessPre_pointed f h
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_congr a
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPre f h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPointed q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPointed p ≫ (pre e).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity) hd
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportRepresentation.pointedIso
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportRepresentation.cartesianRestrictVertexIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_symm, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_comp]
  rw [ha]
  apply Iso.ext
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map, eqToHom_map]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportRepresentation (cartesianRestrict_pointedIso)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
