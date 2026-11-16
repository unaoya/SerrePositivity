module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
概要：全モナドの添字である有限順序集合の圏の nerve と順序和を指定する。
方針：空順序集合を含む Δ₊ の nerve を宇宙持ち上げし、順序和を全次数で適用する。
規約：空順序集合が恒等自己関手、一点順序集合が一回のモナドを添字付ける。
使われ方：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の全モナドの表示。
Riehl–Verity, Homotopy coherent adjunctions and the formal theory of monads,
Remark 3.3.8 の順序和による walking monad の Hom を使う。
Kerodon Remark 6.2.1.4（Tag 02EN）の二胞体へ忘却する前の全添字を保持する。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：walking monad の自己 Hom の全単体集合。
方針：Δ₊ の nerve を指定宇宙に持ち上げる。規約：空順序集合も含める。
使われ方：HA §4.7.2、Riehl–Verity Remark 3.3.8 のモナドの全表示。 -/
abbrev WalkingMonadShape : SSet.{u} :=
  SSet.uliftFunctor.{u, 0}.obj (nerve AugmentedSimplexCategory)

/-- 概要：空順序集合の定値単体を指定する。
方針：各次数で空順序集合を値とする定値関手を作る。
規約：walking monad の合成の単位。使われ方：HA §4.7.2 の単位付きモナド。 -/
def walkingMonadUnit : 𝟙_ SSet.{u} ⟶ WalkingMonadShape where
  app n := ↾fun _ ↦ ULift.up ((Functor.const (Fin (n.unop.len + 1))).obj
    (WithInitial.star : AugmentedSimplexCategory))
  naturality _ _ _ := rfl

/-- 概要：全ての次元の有限順序集合の列を順序和で合成する。
方針：同じ長さの二つの列の積を取り、順序和関手へ後合成する。
規約：両因子の単体作用と同時に可換する全単体写像。
使われ方：HA §4.7.2–§4.7.3、Riehl–Verity Remark 3.3.8 の全合成。 -/
def walkingMonadComposition :
    WalkingMonadShape.{u} ⊗ WalkingMonadShape.{u} ⟶ WalkingMonadShape.{u} where
  app _ := ↾fun p ↦ ULift.up (p.1.down.prod' p.2.down ⋙ tensor AugmentedSimplexCategory)
  naturality _ _ _ := rfl

/-- 概要：一点順序集合によるモナドの一回の適用の添字。
方針：Δ₊ の零単体を持ち上げる。規約：空順序集合の単位とは区別する。
使われ方：HA Proposition 4.7.3.3 の underlying endofunctor。 -/
def walkingMonadGenerator : WalkingMonadShape.{u} _⦋0⦌ :=
  ULift.up (ComposableArrows.mk₀ (WithInitial.of ⦋0⦌ : AugmentedSimplexCategory))

/-- 概要：全合成の各次数は元の順序和関手の後合成である。
方針：指定した単体写像の定義。規約：宇宙持ち上げを外して比較する。
使われ方：HA §4.7.2 の指定積の計算。 -/
lemma walkingMonadComposition_apply (n : SimplexCategoryᵒᵖ)
    (x y : WalkingMonadShape.{u}.obj n) :
    ((walkingMonadComposition).app n (x, y)).down =
      x.down.prod' y.down ⋙ tensor AugmentedSimplexCategory := rfl

end SerrePositivity.InfinityCategories.HA.Monads
