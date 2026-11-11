module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeArrowComp

/-!
概要：次数 −1 の指定全自然元を閉零次数比較で後合成する。
方針：符号付き自然性と厳密比較の全次数自然性を結合則で合成する。
規約：元斉次元と符号を保持する。
使われ方：実回転 square から作る cone 比較の指定零化成分。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories

/-- 概要：元次数 −1 族の閉零次数後合成は同じ符号付き全自然性を持つ。
方針：全次数の二自然性と指定次数での結合則を使用する。
規約：符号を変更しない。使われ方：指定 cone square 入力の全自然性。 -/
lemma dgNegativeNaturalPostcomposition {R : Type u} [CommRing R]
    {D : Type v} [DGCategory R D] {A B C A' B' C' : D}
    (a : GradedHom R A B (-1)) (b : GradedHom R B C 0)
    (a' : GradedHom R A' B' (-1)) (b' : GradedHom R B' C' 0)
    {n : ℤ} (f : GradedHom R A A' n) (g : GradedHom R B B' n)
    (k : GradedHom R C C' n)
    (ha : compose R g a (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R a' f (sub_eq_add_neg n 1).symm)
    (hb : compose R b' g (add_zero n) = compose R k b (zero_add n)) :
    compose R k (compose R b a (add_zero (-1))) (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R (compose R b' a' (add_zero (-1))) f
        (sub_eq_add_neg n 1).symm := by
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum a b k (add_zero (-1))
    (zero_add n) (neg_add_eq_sub 1 n)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum a g b' (neg_add_eq_sub 1 n)
    (add_zero n) (add_zero (n - 1))
  have h₃ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum f a' b' (sub_eq_add_neg n 1).symm
    (add_zero (-1)) (add_zero (n - 1))
  calc
    _ = compose R (compose R k b (zero_add n)) a (neg_add_eq_sub 1 n) := h₁
    _ = compose R (compose R b' g (add_zero n)) a (neg_add_eq_sub 1 n) :=
      congrArg (fun t => compose R t a (neg_add_eq_sub 1 n)) hb.symm
    _ = compose R b' (compose R g a (neg_add_eq_sub 1 n)) (add_zero (n - 1)) := h₂.symm
    _ = compose R b' (n.negOnePow • compose R a' f (sub_eq_add_neg n 1).symm)
        (add_zero (n - 1)) := congrArg (fun t => compose R b' t (add_zero (n - 1))) ha
    _ = n.negOnePow • compose R b' (compose R a' f (sub_eq_add_neg n 1).symm)
        (add_zero (n - 1)) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right _ _ _ _
    _ = _ := congrArg (fun t => n.negOnePow • t) h₃
end SerrePositivity.KST.SConstruction
