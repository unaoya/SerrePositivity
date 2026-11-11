module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalRelativeConstant
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportJointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningCandidate
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationMappingSpaces

/-!
概要：coherent な straightening 写像の fibration の頂点での値の同定。
方針：定値なパラメーターでの対角評価を通常の strict transport 図式へ戻し、内部 Hom の零単体を計算する。
規約：図式の値の反転を施さない既存の leftStraighteningCandidate と比較する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、構成した分類関手の対象での値の検証。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：射列の undercategory の図式への相対 Hom はその射列を strict transport で写した図式と一致する。
方針：各対象の相対関手空間と各射での undercategory による前合成を比較する。
規約：有限順序の ULift からの関手を使って二つの表示の宇宙を揃える。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、Corollary 5.6.0.6（Tag 028T）、定値パラメーターの計算。 -/
lemma strictTransportSimplex_relativeFunctorKanDiagram
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorKanDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram σ) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p) =
      (⟨ULift.down, fun _ _ h ↦ h⟩ :
        ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  rfl

/-- 概要：strict transport の対角単体の fibration パラメーターを固定すると既存の Kan 値図式の coherent 単体になる。
方針：coherent 頂点の定値単体、対角評価の定値図式の式、射列上の相対 Hom の式を順に使う。
規約：底の単体 σ は任意の次数と退化を許す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手の頂点での図式全体の同定。 -/
lemma strictTransportDiagonalSimplex_constant
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportDiagonalSimplex σ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityVertex p) n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p)).app
        (Opposite.op ⦋n⦌) (ULift.up σ) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram σ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf p)) n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveVertex_constant, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation_constant,
    strictTransportSimplex_relativeFunctorKanDiagram]

/-- 概要：coherent な straightening 写像は fibration p の頂点を既存の strict transport の coherent 図式へ写す。
方針：内部 Hom の零単体を任意の底の単体で評価し、定値パラメーターの対角単体の式を適用する。
規約：図式全体の厳密な等式であり、各対象の値だけの一致ではない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手の対象への作用の整合性。 -/
lemma leftStraighteningCoherentMap_vertex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap C).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityVertex p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro σ
  exact strictTransportDiagonalSimplex_constant p σ.down

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
