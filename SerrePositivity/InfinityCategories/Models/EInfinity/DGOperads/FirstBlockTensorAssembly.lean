module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstBlockFamilyAssembly
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionFirstBlockFull

/-!
模型。文献の定義との比較は後で
# 先頭ブロックの再結合を係数列と入力列へ分離する

概要：Berger–Moerdijk §1 の二段の全合成で、まとめた演算の係数と入力を独立に再結合する。
方針：一般の arity 表示の移送を先頭ブロックの arity 族へ適用する。
規約：係数族と入力族は独立な複体族として扱う。
使われ方：全合成の係数側と入力側の結合則を同じ再結合射へ適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：まとめた先頭ブロックの再結合は二つの複体族へ独立に分かれる（Berger–Moerdijk §1）。
方針：arity の表示を移送した先頭の分離則に具体的な先頭ブロックの族を代入する。
規約：両族の先頭の arity は元の前半の和。
使われ方：Schur 演算の係数と入力を分離して結合則を適用する。 -/
lemma firstBlockFamilyAssembly_tensor (D E : ℕ → Complex A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly (fun r => D r ⊗ E r) n m s ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (1 + m) (fun j => D (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j))
        (fun j => E (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j))).hom =
    ((D (∑ j : Fin n, s (j.castAdd m)) ⊗ E (∑ j : Fin n, s (j.castAdd m))) ◁
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso m (fun j => D (s (j.natAdd n))) (fun j => E (s (j.natAdd n)))).hom) ≫
      tensorμ (D (∑ j : Fin n, s (j.castAdd m))) (E (∑ j : Fin n, s (j.castAdd m)))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => D (s (j.natAdd n))))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => E (s (j.natAdd n)))) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly D n m s ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly E n m s) := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly_tensor D E m (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s)
    (∑ j : Fin n, s (j.castAdd m)) (fun j => s (j.natAdd n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_head n m s).symm
    (funext fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_tail n m s j).symm)

namespace Operad

/-- 概要：オペラッド係数の先頭ブロックの再結合は一般の複体族の再結合と一致する（Berger–Moerdijk §1）。
方針：二つの射の定義を比較し、等式の証明の一意性を使う。
規約：オペラッド固有の部分合成を再結合射の中には含めない。
使われ方：係数側の既存の結合則と一般のテンソル分離則を接続する。 -/
lemma firstBlockFamilyAssembly_arity (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly P.arity n m s = P.firstBlockAssembly n m s := by
  rfl

end Operad
end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
