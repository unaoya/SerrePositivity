module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ResolutionSpanNormalization
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FrameSpanNerve

/-!
# 元の E 代数の Map^h の全単体から特殊な三本矢への図式

概要：任意の可換環上の実際の Map^h の全単体を Dwyer–Kan §7 の共通対象へ送る。
方針：元の二つの関手的分解と実際の転送モデル構造を局所的に代入する。
規約：元の代数に cofibrancy・fibrancy、基礎環に標数条件を要求しない。
使われ方：DK Hom と同じ Map^h の高次比較の具体的な共通図式。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory _root_.HomotopicalAlgebra Opposite
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：実際の E 代数モデルの特殊な三本矢の圏（Dwyer–Kan §7）。
方針：同じ転送モデル構造を局所的に選び、実際の両脚の類を使う。
規約：同じ対象と代数射を保持する。
使われ方：元の Map^h の全単体の共通比較先。 -/
abbrev algebraSpecialHammock (X Y : (operad A).Algebra) :=
  let := modelCategory A
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y

/-- 概要：元の Map^h の全単体を実際の特殊な三本矢へ送る（Dwyer–Kan §7）。
方針：同じ二つの関手的分解を全単体の一般の図式に代入する。
規約：Map^h・元の分解・fibrant 置換・全単体作用素を変更しない。
使われ方：高次比較の frame 側の実際の関手。 -/
def mappingSpaceSpecialHammockFunctor (X Y : (operad A).Algebra) :
    ((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ ⥤ algebraSpecialHammock A X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.chosenResolutionSpanFunctor (mappingCofibrantFactorization A)
    (mappingFibrantFactorization A) X Y

/-- 概要：実際の共通図式の左の全縦射は同じ擬同型（Dwyer–Kan §7）。
方針：元の両脚からの弱同値性と実際の転送モデル構造の判定を使う。
規約：元の対象に追加の cofibrancy を仮定しない。
使われ方：特殊な hammock の元の全可換列。 -/
lemma mappingSpaceSpecialHammockFunctor_left_quasiIso {X Y : (operad A).Algebra}
    {s t : ((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ} (f : s ⟶ t) :
    QuasiIso (((mappingSpaceSpecialHammockFunctor A X Y).map f).left).hom := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock.left_weakEquivalence
    ((mappingSpaceSpecialHammockFunctor A X Y).map f)

/-- 概要：実際の共通図式の右の全縦射も同じ擬同型（Dwyer–Kan §7）。
方針：元の両右脚の比較からの弱同値性を実際のモデルへ代入する。
規約：元の代数と元の右の縦射を保持する。
使われ方：高次比較の共通図式の全縦射の条件。 -/
lemma mappingSpaceSpecialHammockFunctor_right_quasiIso {X Y : (operad A).Algebra}
    {s t : ((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ} (f : s ⟶ t) :
    QuasiIso (((mappingSpaceSpecialHammockFunctor A X Y).map f).right).hom := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock.right_weakEquivalence
    ((mappingSpaceSpecialHammockFunctor A X Y).map f)

/-- 概要：元の Map^h の零単体の三本矢は同じ元の局所化射（Dwyer–Kan §7）。
方針：同じ関手的分解の一般の正規化を実際の転送モデルへ代入する。
規約：元の π₀ 同値と元の零単体を保持する。
使われ方：実際の E2b の高次比較の零次の照合。 -/
lemma mappingSpaceSpecialHammockValue_zero (X Y : (operad A).Algebra)
    (f : (((mappingSpace A).obj (op X)).obj Y) _⦋0⦌) :
    let := modelCategory A
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.value ((mappingSpaceSpecialHammockFunctor A X Y).obj
        (op ((((mappingSpace A).obj (op X)).obj Y).elementsMk (op ⦋0⦌) f))) =
      mappingSpacePiZeroEquiv A (weakEquivalences (operad A).Algebra).Q
        (op X) Y (SSet.π₀.mk f) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.chosenResolutionSpanValue_zero (mappingCofibrantFactorization A)
    (mappingFibrantFactorization A) X Y f

/-- 概要：実際の Map^h の全単体の図式は特殊な三本矢の nerve の射を与える（Dwyer–Kan）。
方針：元の同じ関手的分解と Hom の宇宙だけを上げた要素圏を使う。
規約：元の Map^h の単体を保持する。比較の弱同値性は後続。
使われ方：E2b の高次比較の実際の frame 側の射。 -/
def mappingSpaceSpecialHammockNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (algebraSpecialHammock A X Y) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.chosenResolutionSpanNerveMap (mappingCofibrantFactorization A)
    (mappingFibrantFactorization A) X Y

end SerrePositivity.EInfinity.BarrattEccles
