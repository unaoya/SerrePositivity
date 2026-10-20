module

public import SerrePositivity.EInfinity.FrameHom.SimplexTerminalAugmentation
public import SerrePositivity.EInfinity.FrameHom.ResolutionSpanNormalization

/-!
# 全単体の共通比較の両射の元の局所化値

概要：反対要素圏の任意の頂点で三本矢と終端 augmentation の局所化値を照合する。
方針：終端パラメータの制限を要素圏の実際の射にし、三本矢の値の保存を使う。
規約：零単体の要素に限定せず全単体の要素を扱う。
使われ方：Dwyer–Kan §7 の共通比較の両射の同じ π₀ 正規化。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.EInfinity.FrameHom

open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex
open scoped Simplicial

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- 概要：共通比較の全頂点で元の局所化射は一致する（Dwyer–Kan §7）。
方針：終端パラメータの実際の要素圏射と元の零次の正規化を合成する。
規約：全ての次数の元の単体を保持する。
使われ方：高次比較の両射と既存の π₀ 比較の照合。 -/
lemma chosenResolutionSpanValue_augmentation
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X Y : C) (s : ((((chosenResolutionHom cof fib).obj (op X)).obj Y).Elements)ᵒᵖ) :
    SpecialHammock.value ((chosenResolutionSpanFunctor cof fib X Y).obj s) =
      chosenResolutionHomPiZeroEquiv (weakEquivalences C).Q cof fib (op X) Y
        (SSet.π₀.mk ((SimplexTerminalAugmentation.augmentation
          (((chosenResolutionHom cof fib).obj (op X)).obj Y)).app (op ⦋0⦌)
            (ComposableArrows.mk₀ s))) := by
  let K := ((chosenResolutionHom cof fib).obj (op X)).obj Y
  let z := (SimplexTerminalAugmentation.augmentation K).app (op ⦋0⦌)
    (ComposableArrows.mk₀ s)
  let e := op (K.elementsMk (op ⦋0⦌) z)
  let f : e ⟶ s := Quiver.Hom.op (Functor.Elements.homMk
    (SimplexTerminalAugmentation.parameter K (ComposableArrows.mk₀ s)).op rfl)
  exact (chosenResolutionSpanValue_naturality cof fib X Y f).symm.trans
    (chosenResolutionSpanValue_zero cof fib X Y z)

end SerrePositivity.EInfinity.FrameHom
