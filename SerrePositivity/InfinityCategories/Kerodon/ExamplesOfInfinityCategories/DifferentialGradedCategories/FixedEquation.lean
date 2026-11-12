module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! # 固定した端点・次数での方程式の検証

概要：一集合の方程式は一組の有効な端点・次数で検証すれば十分で、型付き射の式からも移せる。
方針：端点と次数の一意性、および微分の異種等号の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：型付き Hom-fiber の解から未知集合の方程式を検証する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：有効な一組の端点・次数で成り立つ方程式はその集合の全ての指定で成り立つ。
方針：端点と次数の一意性で指定を同定し、証明の一意性を使う。
規約：HA Construction 1.3.1.6。使われ方：固定した座標の式から Equation を構成する。 -/
lemma equation_of_fixed {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a₀ b₀ : Fin (n + 1)) (k₀ : ℤ)
    (hI : 2 ≤ I.card) (ha₀ : a₀ = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb₀ : b₀ = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk₀ : k₀ = 2 - (I.card : ℤ))
    (heq : differential A (s.hom I a₀ b₀ k₀ hI ha₀ hb₀ hk₀) =
      s.rhs I a₀ b₀ k₀ hI ha₀ hb₀ hk₀) : s.Equation I := by
  intro a b k hI' ha hb hk
  have hA : a = a₀ := ha.trans ha₀.symm
  have hB : b = b₀ := hb.trans hb₀.symm
  have hK : k = k₀ := hk.trans hk₀.symm
  cases hA
  cases hB
  cases hK
  exact heq

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (equation_of_fixed)


/-- 概要：一集合の成分と右辺が型付きの微分方程式に異種等号で一致すれば、その集合の方程式が成り立つ。
方針：微分の異種等号を使って固定座標の式を戻し、端点・次数の一意性を使う。
規約：HA Proposition 1.3.1.10。使われ方：明示解の δa=r₀ を先頭集合の方程式へ戻す。 -/
lemma equation_of_fixed_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    {X Y : D} {l : ℤ} (hx : s.obj a = X) (hy : s.obj b = Y) (hkl : k = l)
    (f : GradedHom A X Y l) (r : GradedHom A X Y (l + 1))
    (hf : HEq (s.hom I a b k hI ha hb hk) f)
    (hr : HEq (s.rhs I a b k hI ha hb hk) r) (heq : differential A f = r) :
    s.Equation I := by
  apply s.equation_of_fixed I a b k hI ha hb hk
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) hx hy hkl _ _ hf
  exact eq_of_heq (hd.trans ((heq_of_eq heq).trans hr.symm))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (equation_of_fixed_heq)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
