module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionCoefficientValues
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomClassificationIsoLaws

/-!
概要：指定底変換の初頂点制限の端点を揃え、同じ分類射の逆を保持する。
方針：既存の共役表示・端点正規化・分類の逆射の法則を使う。
規約：指定底変換も標準同型も選び直さない。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の合成則の降下。
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
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance simplexPastingInputs_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：指定底変換の制限は、同じ始域に正規化すると元の係数共役そのもの。
方針：初頂点の自然性による始域移送を除き、同じ共役表示を使う。
規約：同型の等式。使われ方：中間制限同型の相殺。 -/
lemma leftStraightening_baseChange_simplex_normalized
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc])
      rfl
      ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D))) =
      (leftClassificationSimplexIso p).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k))) ≪≫
        (simplexSectionBaseChangeCoefficient p k).symm ≪≫
        (leftClassificationSimplexIso (pullback.snd p k)).symm := by
  exact eq_of_heq ((diagramIsoCongr_heq _ _ _).trans
    (leftStraightening_baseChange_firstVertex_coefficient p k))

/-- 概要：正規化した同じ指定底変換は対象別制限同型と同じ係数比較を結ぶ。
方針：元の共役表示の終わりの逆同型を相殺する。
規約：同じ射の等式。使われ方：二段の底変換の相殺の計算。 -/
lemma leftStraightening_baseChange_simplex_intertwining
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    (diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc])
      rfl
      ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D)))).hom ≫
      (leftClassificationSimplexIso (pullback.snd p k)).hom =
      ((leftClassificationSimplexIso p).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)))).hom ≫
        (simplexSectionBaseChangeCoefficient p k).inv := by
  rw [leftStraightening_baseChange_simplex_normalized]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：元の底上の同型を分類した射は、同じ逆射の分類を逆に持つ。
方針：既存の分類の逆射の二つの合成則を使う。
規約：元の同型の像を変えない。使われ方：標準引き戻し比較の分類後の相殺。 -/
lemma leftClassificationHom_preserves_iso {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : E ≅ H) (he : e.hom ≫ q = p) (hi : e.inv ≫ p = q) :
    IsIso (leftClassificationHom p q e.hom he) := by
  exact ⟨⟨leftClassificationHom q p e.inv hi,
    leftClassificationHom_iso_hom_inv p q e he hi,
    leftClassificationHom_iso_inv_hom p q e he hi⟩⟩

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
