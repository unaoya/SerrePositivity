module

public import SerrePositivity.InfinityCategories.F1.Diagrams.DiagonalRelativeConstant
public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportJointEvaluation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningCandidate
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationMappingSpaces

/-!
概要：coherent な straightening 写像の fibration の頂点での値の同定。
方針：定値なパラメーターでの対角評価を通常の strict transport 図式へ戻し、内部 Hom の零単体を計算する。
規約：図式の値の反転を施さない既存の leftStraighteningCandidate と比較する。
使われ方：Kerodon Corollary 5.6.0.6、構成した分類関手の対象での値の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：射列の undercategory の図式への相対 Hom はその射列を strict transport で写した図式と一致する。
方針：各対象の相対関手空間と各射での undercategory による前合成を比較する。
規約：有限順序の ULift からの関手を使って二つの表示の宇宙を揃える。
使われ方：Kerodon Construction 5.3.1.5、Corollary 5.6.0.6、定値パラメーターの計算。 -/
lemma strictTransportSimplex_relativeFunctorKanDiagram
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    relativeFunctorKanDiagram (strictTransportSimplexUnderDiagram σ) (leftFibrationObjectOf p) =
      (⟨ULift.down, fun _ _ h ↦ h⟩ :
        ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙ σ ⋙ leftStrictTransportFunctor p := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  rfl

/-- 概要：strict transport の対角単体の fibration パラメーターを固定すると既存の Kan 値図式の coherent 単体になる。
方針：coherent 頂点の定値単体、対角評価の定値図式の式、射列上の相対 Hom の式を順に使う。
規約：底の単体 σ は任意の次数と退化を許す。
使われ方：Kerodon Corollary 5.6.0.6、分類関手の頂点での図式全体の同定。 -/
lemma strictTransportDiagonalSimplex_constant
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    strictTransportDiagonalSimplex σ (PinchedHom.constant (leftFibrationInfinityVertex p) n) =
      (kanDiagramCoherentNerve (leftStrictTransportFunctor p)).app
        (Opposite.op ⦋n⦌) (ULift.up σ) := by
  change diagonalRelativeEvaluation (strictTransportSimplexUnderDiagram σ)
    (PinchedHom.constant (coherentNerveVertex (leftFibrationObjectOf p)) n) =
      enrichedFunctorOfOrderDiagram _
  rw [coherentNerveVertex_constant, diagonalRelativeEvaluation_constant,
    strictTransportSimplex_relativeFunctorKanDiagram]

/-- 概要：coherent な straightening 写像は fibration p の頂点を既存の strict transport の coherent 図式へ写す。
方針：内部 Hom の零単体を任意の底の単体で評価し、定値パラメーターの対角単体の式を適用する。
規約：図式全体の厳密な等式であり、各対象の値だけの一致ではない。
使われ方：Kerodon Corollary 5.6.0.6、分類関手の対象への作用の整合性。 -/
lemma leftStraighteningCoherentMap_vertex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    (leftStraighteningCoherentMap C).app (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p) =
      functorVertex (leftStraighteningCandidate p) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro σ
  exact strictTransportDiagonalSimplex_constant p σ.down

end SerrePositivity.InfinityCategories
