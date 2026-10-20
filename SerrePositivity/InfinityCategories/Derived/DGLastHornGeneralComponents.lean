module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralFiller

/-! # 一般最後外ホーンの二未知解と実充填単体の同じ成分

概要：実充填単体の欠面最上位成分・全体最上位成分は、入力の同じ Q・A。
方針：二度の指定成分置換の評価と、欠面が全体集合と異なることを使う。
規約：選択や同型で置き換えない。使われ方：高次残差 cone の二座標との実照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable {σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D}

/-- Q 挿入後の欠面の指定成分は、入力 Q そのもの。 -/
lemma dgGeneralLastHornQData_component
    (Q : GradedHom A ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj (dgLastHornPenultimate n)) (-(n : ℤ))) :
    (dgGeneralLastHornQData σ Q).hom (dgLastHornMissingIndex n) 0
      (dgLastHornPenultimate n) (-(n : ℤ)) (dgLastHornMissingIndex_two n)
      (dgLastHornMissingIndex_min n) (dgLastHornMissingIndex_max n)
      (dgLastHornMissingIndex_degree n) = Q :=
  SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

variable (S : DGGeneralLastHornSolution σ)

/-- 一般充填単体は、元の回収対象族を厳密に保持する。 -/
lemma DGGeneralLastHornSolution.simplex_obj (i : Fin (n + 3)) :
    S.simplex.obj i = (HornData.knownData σ).obj i := rfl

/-- 一般充填単体の欠面最上位成分は、同じ入力 Q。 -/
lemma DGGeneralLastHornSolution.simplex_Q :
    S.simplex.hom (dgLastHornMissingIndex n) 0 (dgLastHornPenultimate n) (-(n : ℤ))
      (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
      (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n) = S.Q :=
  (SimplexData.replaceFixed_hom_of_ne (dgGeneralLastHornQData σ S.Q) Finset.univ
    0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (dgLastHornTop_two n)
    (dgLastHornTop_min n) (dgLastHornTop_max n) (dgLastHornTop_degree n) S.a
    (dgLastHornMissingIndex n) 0 (dgLastHornPenultimate n) (-(n : ℤ))
    (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
    (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n)
    (dgLastHornMissingIndex_ne_univ n)).trans (dgGeneralLastHornQData_component S.Q)

/-- 一般充填単体の最上位成分は、同じ入力 A。 -/
lemma DGGeneralLastHornSolution.simplex_A :
    S.simplex.hom Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (dgLastHornTop_two n)
      (dgLastHornTop_min n) (dgLastHornTop_max n) (dgLastHornTop_degree n) = S.a :=
  SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
