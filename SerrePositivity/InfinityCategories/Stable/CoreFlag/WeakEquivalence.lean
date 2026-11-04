module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.DoubleSimplicialDiagonal
public import SerrePositivity.InfinityCategories.F1.CoreFlag.Basic
public import SerrePositivity.InfinityCategories.F1.CoreFlag.RowComparison

/-!
分割で生成：docstring を書き直すこと
概要：一般 core 旗の対角評価の弱ホモトピー同値。
方針：転置した行の定数包含に行弱同値の対角定理を適用し、切断恒等式で消去する。
規約：頂点評価を旗次数について自然と扱わない。単体集合のモデル構造は使わない。
使われ方：Sp-8、K-cof に供給する一般 core 旗比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories
open EInfinity.Hammock.DoubleSimplicial

/-- 転置の前後の対角は、恒等な次数成分で自然に同型。 -/
def diagonalTransposeIso (C : SSet.{u}) :
    diagonalFunctor.obj (transposeResolution C) ≅ diagonal C :=
  NatIso.ofComponents (fun n ↦ Iso.refl _) (by
    intro n m f
    change (((resolution C).obj n).map f ≫ ((resolution C).map f).app m) ≫ 𝟙 _ =
      𝟙 _ ≫ (((resolution C).map f).app n ≫ ((resolution C).obj m).map f)
    simpa only [Category.comp_id, Category.id_comp] using ((resolution C).map f).naturality f)

/-- 対角上の行定数包含は、元の同じ定数包含。 -/
lemma diagonal_bisimplicialInclusion (C : SSet.{u}) :
    (diagonalConstantIso C).inv ≫ diagonalFunctor.map (bisimplicialInclusion C) ≫
      (diagonalTransposeIso C).hom = inclusion C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.KST.LocalizingInvariants.CoreFlag
