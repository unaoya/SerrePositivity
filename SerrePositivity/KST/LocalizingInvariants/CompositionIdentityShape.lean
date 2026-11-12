module

public import SerrePositivity.KST.LocalizingInvariants.SquareDiagonalShape

/-!
概要：恒等射を含む標準三角形の辺比較に使う退化格子を計算する。
方針：有限順序写像の各頂点で、退化後の全格子が第一射影であることを示す。
規約：全単体次数での射の等号。使われ方：置換単位の右辺表示の恒等因子を消す。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CompositionIdentity

lemma post_degenerate : SquareDiagonal.postShape ≫ stdSimplex.σ (1 : Fin 2) =
    fst (Δ[1] : SSet.{u}) Δ[1] := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply SSet.stdSimplex.ext
  intro i
  change (1 : Fin 2).predAbove (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.postIndex (s i, t i)) = s i
  generalize hs : s i = a
  generalize ht : t i = b
  fin_cases a <;> fin_cases b <;> rfl

lemma pre_degenerate : SquareDiagonal.preShape ≫ stdSimplex.σ (0 : Fin 2) =
    fst (Δ[1] : SSet.{u}) Δ[1] := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply SSet.stdSimplex.ext
  intro i
  change (0 : Fin 2).predAbove (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.preIndex (s i, t i)) = s i
  generalize hs : s i = a
  generalize ht : t i = b
  fin_cases a <;> fin_cases b <;> rfl

end SerrePositivity.KST.LocalizingInvariants.CompositionIdentity
