module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearPullback
public import Mathlib.Algebra.Module.TransferInstance

/-! # dg nerve の右 pinched 写像空間の単体的 A 加群構造

概要：全次数の線形表示で実際の単体に A 加群構造を移し、全ての引き戻しを線形にする。
方針：同値から加法群と加群構造を移し、線形模型の引き戻しを共役する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形ホーン充填と写像空間の代数。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：実際の右 pinched 写像空間の各次数は加法可換群。
方針：全次数の線形表示の同値に沿って加法群を移す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：各次数の加法と零・負元。 -/
instance instRawAddCommGroup (x y : D) (n : ℕ) :
    AddCommGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) n) := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y n).addCommGroup

/-- 概要：単体的集合として表記した右 pinched 単体にも同じ加法群構造を与える。
方針：内部の単体型の構造を定義上一致する評価の型で再公開する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：元の SSet の各次数での型クラス推論。 -/
instance instAddCommGroup (x y : D) (n : ℕ) :
    AddCommGroup ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) := instRawAddCommGroup x y n

/-- 概要：実際の右 pinched 写像空間の各次数は A 加群。
方針：線形表示の加法同値に沿って A の作用と加群則を移す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：実際の単体の A スカラー倍。 -/
instance instRawModule (x y : D) (n : ℕ) :
    Module A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) n) := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y n).addEquiv).module A

/-- 概要：単体的集合として表記した右 pinched 単体にも同じ A 加群構造を与える。
方針：内部の単体型の加群を評価の型で再公開し、操作を共有する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：元の SSet の各次数での A 加群の型クラス推論。 -/
instance instModule (x y : D) (n : ℕ) :
    Module A ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) := instRawModule x y n

/-- 概要：全次数の線形表示の同値は、移した加群構造について A 線形同値。
方針：構造移送の加法同値を線形同値として読む。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：実際の写像空間と線形解の A 線形な比較。 -/
def moduleEquiv (x y : D) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌ ≃ₗ[A] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y n).addEquiv).linearEquiv A

/-- 概要：加群の比較の値は元の成分回収による線形単体。
方針：構造移送の線形同値の順写像を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：自然性と線形成分の評価。 -/
lemma moduleEquiv_apply (x y : D) (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) :
    moduleEquiv x y n s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s := rfl

variable {x y : D}

/-- 概要：任意の添字写像による引き戻しは実際の単体の間の A 線形写像。
方針：線形模型の引き戻しを両次数の線形同値で共役する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：全ての面・退化の線形性。 -/
def pullbackLinear {m n : SimplexCategory} (α : m ⟶ n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n.len⦌ →ₗ[A] (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋m.len⦌ :=
  (moduleEquiv x y m.len).symm.toLinearMap ∘ₗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback α.toOrderHom ∘ₗ
    (moduleEquiv x y n.len).toLinearMap

/-- 概要：構成した線形写像の値は元の右 pinched 単体の引き戻し。
方針：線形表示の自然性と線形同値の逆則を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：元の単体的構造と線形写像の一致。 -/
lemma pullbackLinear_apply {m n : SimplexCategory} (α : m ⟶ n)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n.len⦌) : pullbackLinear α s = s.pullback α := by
  apply (moduleEquiv x y m.len).injective
  simp only [pullbackLinear, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, moduleEquiv_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback s α).symm

/-- 概要：元の右 pinched 単体の引き戻しは加法を保つ。
方針：構成した線形写像と元の引き戻しの一致を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：面・退化の加法性。 -/
lemma pullback_add {m n : SimplexCategory} (α : m ⟶ n)
    (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n.len⦌) :
    (s + t).pullback α =
      (s.pullback α + t.pullback α : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋m.len⦌) := by
  simpa only [pullbackLinear_apply] using map_add (pullbackLinear (x := x) (y := y) α) s t

/-- 概要：元の右 pinched 単体の引き戻しは A スカラー倍を保つ。
方針：構成した線形写像と元の引き戻しの一致を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：面・退化の A 線形性。 -/
lemma pullback_smul {m n : SimplexCategory} (α : m ⟶ n) (c : A)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n.len⦌) :
    (c • s).pullback α =
      (c • s.pullback α : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋m.len⦌) := by
  simpa only [pullbackLinear_apply] using map_smul (pullbackLinear (x := x) (y := y) α) c s

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
