module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramOrdinaryAction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorActionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeBaseChangeComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinityEquivalence

/-!
概要：元の底上の射の共同切断への作用を、同じ後合成の通常の自然変換として読む。
方針：既存の相対後合成を各成分で評価し、豊穣表示の一致を全単体で確認する。
規約：法則の計算に追加の自然性の仮定を置かない。
使われ方：Kerodon §5.6（Tag 027M）・Corollary 5.6.0.6（Tag 028T）の
分類で、元の標準引き戻し貼り合わせ射と共同切断比較を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

/-- 概要：元の全空間射による相対後合成を同じ切断図式全体の自然変換として読む。
方針：各成分に既存の後合成を使い、前合成との既存の可換式で束ねる。
規約：元の射と任意の底上の反変図式を保つ。使われ方：共同実現の射作用の計算。 -/
def relativeSectionPostTransformation
    {E H B : SSet.{u}} (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) :
    (relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf p) ⋙ kanObjectForget ⟶
      (relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf q) ⋙ kanObjectForget where
  app j := relativeFunctorPost p q f hf (A.obj (Opposite.op j)).hom
  naturality {_ _} g := relativeFunctorPost_overPre p q f hf (A.map g.op)

/-- 概要：元の後合成の自然変換は、同じ実射の豊穣作用の単位からの表示。
方針：元の相対関手の各次数で同じ後合成を計算する。
規約：元の射の全パラメーターの表示の等式。使われ方：通常の辺の実現への接続。 -/
lemma relativeSectionPostTransformation_eHom
    {E H B : SSet.{u}} (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) :
    eHomEquiv SSet.{u} (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from
        Over.homMk (U := Over.mk p) (V := Over.mk q) f hf) ≫
      (relativeSectionEnrichedDiagram A).toEnrichedFunctor.map
        (leftFibrationObjectOf p) (leftFibrationObjectOf q) =
      eHomEquiv SSet.{u} (kanDiagramHom
        (F := ⟨(relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf p), trivial⟩)
        (G := ⟨(relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf q), trivial⟩)
        (relativeSectionPostTransformation p q f hf A)) := by
  apply (SSet.unitHomEquiv _).injective
  change ((relativeSectionEnrichedDiagram A).toEnrichedFunctor.map
      (leftFibrationObjectOf p) (leftFibrationObjectOf q)).app (Opposite.op ⦋0⦌)
      (SimplicialCategory.homEquiv' (leftFibrationObjectOf p) (leftFibrationObjectOf q)
        (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from
          Over.homMk (U := Over.mk p) (V := Over.mk q) f hf)) =
    (SSet.unitHomEquiv _) ((SSet.unitHomEquiv _).symm
      (strictDiagramMappingVertex (relativeSectionPostTransformation p q f hf A)))
  rw [leftFibrationHom_vertex, Equiv.apply_symm_apply]
  apply Subtype.ext
  funext j
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro x
  have hα : α = (SimplexCategory.const m.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro k β
  apply ConcreteCategory.hom_ext
  intro y
  change (((relativeFunctorComposition (A.obj (Opposite.op j)) (Over.mk p) (Over.mk q)).app m
      (x, (relativeFunctorSpace q p).map (SimplexCategory.const m.unop ⦋0⦌ 0).op
        (relativeFunctorVertex q p f hf))).val.app k β) y =
    f.app k (x.val.app k β y)
  rw [Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorComposition_apply]
  rfl

/-- 概要：元の射の共同切断実現でのHom作用は、同じ後合成の自然変換の辺の類。
方針：元の豊穣表示の等式を、実際のcoherentな辺の自然性へ渡す。
規約：自然性の入力を別に仮定せず、元の実射から証明した表示を使う。
使われ方：貼り合わせ比較を元の分類Homとして回収する。 -/
lemma relativeSectionRealization_homMk
    {E H B : SSet.{u}} (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) :
    normalizedVertexHomMap (relativeSectionEnrichedDiagram A).realization
      ((relativeSectionEnrichedDiagram A).realization_vertex (leftFibrationObjectOf p)).symm
      ((relativeSectionEnrichedDiagram A).realization_vertex (leftFibrationObjectOf q)).symm
      (Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated) =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨(relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf p), trivial⟩)
        (G := ⟨(relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf q), trivial⟩)
        (relativeSectionPostTransformation p q f hf A)).toTruncated :=
  (relativeSectionEnrichedDiagram A).realization_homMk_of_homEquiv
    (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from
      Over.homMk (U := Over.mk p) (V := Over.mk q) f hf)
    (relativeSectionPostTransformation p q f hf A)
    (relativeSectionPostTransformation_eHom p q f hf A)

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
