module

public import SerrePositivity.KST.LocalizingInvariants.SquareDiagonalShape

/-!
概要：三つの合成射の二つの比較順序を、同じ四頂点単体の全格子に束ねる。
方針：中間の辺を経る三角形族と正方形を有限単調写像で作り、各面を計算する。
規約：第一因子が辺、第二因子が比較。使われ方：標準合成三角形の全 h Fun 貼合せ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CompositionOverlap

def overlapIndex : Fin 2 × Fin 3 →o Fin 4 where
  toFun p := if p.1 = 0 then if p.2 = 0 then 0 else 1 else if p.2 = 2 then 3 else 2
  monotone' := by decide

def squareIndex : Fin 2 × Fin 2 →o Fin 4 where
  toFun p := if p.1 = 0 then p.2.castSucc.castSucc else if p.2 = 0 then 2 else 3
  monotone' := by decide

def overlap : (Δ[1] : SSet.{u}) ⊗ Δ[2] ⟶ Δ[3] := gridMap overlapIndex

def square : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[3] := gridMap squareIndex

lemma overlap_first : (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ overlap.{u} =
    SquareDiagonal.preShape ≫ stdSimplex.δ (3 : Fin 4) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply SSet.stdSimplex.ext
  intro i
  change overlapIndex (s i, (2 : Fin 3).succAbove (t i)) =
    (3 : Fin 4).succAbove (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.preIndex (s i, t i))
  generalize hs : s i = a
  generalize ht : t i = b
  fin_cases a <;> fin_cases b <;> rfl

lemma overlap_last : (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ overlap.{u} =
    SquareDiagonal.postShape ≫ stdSimplex.δ (0 : Fin 4) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply SSet.stdSimplex.ext
  intro i
  change overlapIndex (s i, (0 : Fin 3).succAbove (t i)) =
    (0 : Fin 4).succAbove (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.postIndex (s i, t i))
  generalize hs : s i = a
  generalize ht : t i = b
  fin_cases a <;> fin_cases b <;> rfl

lemma overlap_long : (Δ[1] ◁ stdSimplex.δ (1 : Fin 3)) ≫ overlap.{u} = square := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply SSet.stdSimplex.ext
  intro i
  change overlapIndex (s i, (1 : Fin 3).succAbove (t i)) = squareIndex (s i, t i)
  generalize hs : s i = a
  generalize ht : t i = b
  fin_cases a <;> fin_cases b <;> rfl

lemma square_lower : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ square.{u} = stdSimplex.δ (1 : Fin 4) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.ext
  intro i
  change squareIndex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex.{u} 1).val.1 (s i),
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex.{u} 1).val.2 (s i)) = (1 : Fin 4).succAbove (s i)
  generalize hs : s i = a
  fin_cases a <;> rfl

lemma square_upper : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ square.{u} = stdSimplex.δ (2 : Fin 4) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.ext
  intro i
  change squareIndex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex.{u} 0).val.1 (s i),
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex.{u} 0).val.2 (s i)) = (2 : Fin 4).succAbove (s i)
  generalize hs : s i = a
  fin_cases a <;> rfl

lemma square_source : SSet.ι₀ ≫ square.{u} =
    stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.ext
  intro i
  change squareIndex (s i, 0) =
    (3 : Fin 4).succAbove ((1 : Fin 3).succAbove (s i))
  generalize hs : s i = a
  fin_cases a <;> rfl

lemma square_target : SSet.ι₁ ≫ square.{u} =
    stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.ext
  intro i
  change squareIndex (s i, 1) =
    (0 : Fin 4).succAbove ((1 : Fin 3).succAbove (s i))
  generalize hs : s i = a
  fin_cases a <;> rfl

end SerrePositivity.KST.LocalizingInvariants.CompositionOverlap
