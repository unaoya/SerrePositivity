module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalRelativeConstantBase
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportJointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationCoherentEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：coherent な straightening を底の対象で評価した射の同定。
方針：底の定値単体での undercategory の図式と対角評価を計算する。
規約：対象だけでなく fibration の全ての高次単体での等式を示す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手の評価との整合性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底の対象の定値単体上の undercategory の図式は定値図式になる。
方針：対象の値は定義から計算し、射の値には Under.map の恒等則を使う。
規約：底の単体の次数 n は任意。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、共同評価の底の対象への制限。 -/
lemma strictTransportSimplexUnderDiagram_constant
    {C : Type u} [Category.{u} C] (c : C) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) n) =
      (Functor.const (ULift.{u} (Fin (n + 1)))ᵒᵖ).obj
        (Over.mk (nerveMap (Under.forget c))) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.comp_id]
  apply Over.OverMorphism.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_id c

/-- 概要：底を定値単体に固定した strict transport の対角単体は既存の coherent 評価になる。
方針：底上の図式の定値性と対角評価の定値な底の式を使う。
規約：fibration の coherent 単体 F は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手の対象ごとの高次の作用。 -/
lemma strictTransportDiagonalSimplex_constant_base
    {C : Type u} [Category.{u} C] (c : C) {n : ℕ}
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportDiagonalSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) n) F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportCoherentEvaluation c).app (Opposite.op ⦋n⦌) F := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) n)) F = _
  rw [strictTransportSimplexUnderDiagram_constant, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation_constant_base]
  rfl

/-- 概要：straightening 写像を底の対象 c で評価すると相対 Hom の coherent 評価と一致する。
方針：curry の頂点評価を共同評価の制限に戻し、任意の次数の定値な底の式を使う。
規約：単体集合の射の厳密な等式なので全ての高次パラメーターとの整合性を含む。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手の写像空間での作用を評価する。 -/
lemma leftStraighteningCoherentMap_evaluate
    {C : Type u} [Category.{u} C] (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportCoherentEvaluation c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  exact strictTransportDiagonalSimplex_constant_base c F

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
