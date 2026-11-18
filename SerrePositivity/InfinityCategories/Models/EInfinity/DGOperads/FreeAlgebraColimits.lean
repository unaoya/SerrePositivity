module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FreeAlgebraAdjunction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurColimits

/-!
模型。文献の定義との比較は後で
# 自由・忘却随伴の底の関手の余極限保存

概要：Berger–Moerdijk §1 の自由代数の底は sifted 余極限と filtered 余極限を保つ。
方針：自由関手と忘却関手の合成を Schur 関手に厳密に同定する。
規約：代数の余極限の存在や忘却によるその保存はまだ仮定しない。
使われ方：随伴のモナドの余極限保存と生成射の小対象性を検証する。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A)

/-- 概要：自由代数の底の関手は sifted 余極限を保つ（BM §1）。
方針：底の関手を Schur 関手へ書き換える。
規約：零入力の演算と対称群作用を含む。
使われ方：代数の sifted 余極限の存在をモナドの方法で導く。 -/
instance freeAlgebraForget_preservesSiftedColimits (J : Type u) [SmallCategory J]
    [IsSifted J] :
    PreservesColimitsOfShape J (P.freeAlgebraFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeAlgebraFunctor_forget]
  infer_instance

/-- 概要：自由代数の底の関手は filtered 余極限を保つ（BM §1）。
方針：Schur 関手の filtered 余極限保存を使う。
規約：代数の圏での余極限保存の仮定を要求しない。
使われ方：自由像の生成射に小対象論法を適用する。 -/
instance freeAlgebraForget_preservesFilteredColimits (J : Type u) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J (P.freeAlgebraFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeAlgebraFunctor_forget]
  infer_instance

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
