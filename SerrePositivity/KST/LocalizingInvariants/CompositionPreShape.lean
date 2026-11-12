module

public import SerrePositivity.KST.LocalizingInvariants.CompositionOverlapShape

/-!
概要：共通終点を持つ三辺の比較を、同じ三単体内の全三角形族として構成する。
方針：有限格子の第一列を三頂点、第二列を共通終点へ送って各面を計算する。
規約：全単体次数での等号。使われ方：標準上側比較二つの合成の結合律。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CompositionPre

def index : Fin 2 × Fin 3 →o Fin 4 where
  toFun p := if p.1 = 0 then p.2.castSucc else 3
  monotone' := by decide

def shape : (Δ[1] : SSet.{u}) ⊗ Δ[2] ⟶ Δ[3] := gridMap index

lemma first : (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ shape.{u} =
    SquareDiagonal.preShape ≫ stdSimplex.δ (2 : Fin 4) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply SSet.stdSimplex.ext
  intro i
  change index (s i, (2 : Fin 3).succAbove (t i)) =
    (2 : Fin 4).succAbove (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.preIndex (s i, t i))
  generalize hs : s i = a
  generalize ht : t i = b
  fin_cases a <;> fin_cases b <;> rfl

lemma last : (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ shape.{u} =
    SquareDiagonal.preShape ≫ stdSimplex.δ (0 : Fin 4) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply SSet.stdSimplex.ext
  intro i
  change index (s i, (0 : Fin 3).succAbove (t i)) =
    (0 : Fin 4).succAbove (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.preIndex (s i, t i))
  generalize hs : s i = a
  generalize ht : t i = b
  fin_cases a <;> fin_cases b <;> rfl

lemma long : (Δ[1] ◁ stdSimplex.δ (1 : Fin 3)) ≫ shape.{u} =
    SquareDiagonal.preShape ≫ stdSimplex.δ (1 : Fin 4) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply SSet.stdSimplex.ext
  intro i
  change index (s i, (1 : Fin 3).succAbove (t i)) =
    (1 : Fin 4).succAbove (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.preIndex (s i, t i))
  generalize hs : s i = a
  generalize ht : t i = b
  fin_cases a <;> fin_cases b <;> rfl

end SerrePositivity.KST.LocalizingInvariants.CompositionPre
