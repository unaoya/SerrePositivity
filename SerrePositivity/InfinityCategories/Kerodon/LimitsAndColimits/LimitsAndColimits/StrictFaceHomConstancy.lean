module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathFaces

/-!
概要：厳密な順序図式である面から、元の単体の真部分区間 Hom の定値性を回収する。
方針：区間外の点を除く面は Hom 上で全射であり、定値性をその全射に沿って降下する。
規約：対象の移送は同じ面の豊穣関手の等式で処理する。
使われ方：Ind-S (9b) の二つの指定厳密合成面からの有限座標検証。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


/-- 区間外の頂点を除く面は native Hom 全体へ全射。 -/
lemma pathFaceMap_epi_of_outside {n : ℕ} (j : Fin (n + 2)) (a b : Fin (n + 1))
    (hout : j < j.succAbove a ∨ j.succAbove b < j) : Epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} j a b) := by
  rw [NatTrans.epi_iff_epi_app]
  intro d
  rw [epi_iff_surjective]
  intro P
  have hp : P ∈ (Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} j a b)).obj d := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.range_pathFaceMap]
    intro k hk
    rcases hout with h | h
    · have hh := (P.obj k).left_le (ULift.up j) hk
      exact (not_le_of_gt h) hh
    · have hh := (P.obj k).le_right (ULift.up j) hk
      exact (not_le_of_gt h) hh
  exact hp

/-- 通常の順序図式の全 native Hom は元の射に定値。 -/
lemma orderDiagramHom_exists_const {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (A : J ⥤ C)
    (i j : SimplicialThickening J) (hij : i.as ≤ j.as) :
    ∃ c, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram A).map i j = SSet.const c := by
  refine ⟨SimplicialCategory.homEquiv' _ _ (A.map (homOfLE hij)), ?_⟩
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

/-- 面の等式で指定した厳密図式の Hom 定値性を、その同じ面で回収する。 -/
lemma enrichedHom_exists_const_of_eq_orderDiagram {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet (SimplicialThickening J) C) (A : J ⥤ C)
    (hF : F = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram A)
    (i j : SimplicialThickening J) (hij : i.as ≤ j.as) :
    ∃ c, F.map i j = SSet.const c := by
  subst F
  exact orderDiagramHom_exists_const A i j hij

/-- 区間外の厳密面は、元の native Hom 全体の定値性を与える。 -/
lemma simplexHom_exists_const_of_strict_face
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
    (t : (SimplicialNerve C) _⦋n + 1⦌) (j : Fin (n + 2))
    (A : ULift.{u} (Fin (n + 1)) ⥤ C)
    (ht : (SimplicialNerve C).δ j t = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram A)
    (a b : Fin (n + 1)) (hab : a ≤ b)
    (hout : j < j.succAbove a ∨ j.succAbove b < j) :
    ∃ c, t.map ⟨ULift.up (j.succAbove a)⟩ ⟨ULift.up (j.succAbove b)⟩ = SSet.const c := by
  have := pathFaceMap_epi_of_outside.{u} j a b hout
  obtain ⟨c, hc⟩ := enrichedHom_exists_const_of_eq_orderDiagram
    ((SimplicialNerve C).δ j t) A ht ⟨ULift.up a⟩ ⟨ULift.up b⟩ hab
  refine ⟨c, (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} j a b)).1 ?_⟩
  rw [SSet.comp_const]
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
