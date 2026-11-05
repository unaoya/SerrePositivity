module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.Stable.Verdier.StableCategories
public import SerrePositivity.InfinityCategories.Stable.ZeroDiagramComparison

/-!
分割で生成：docstring を書き直すこと
概要：元の lax pullback に、両因子からの実際の全単体上の包含関手を構成する。
方針：零値関手を端に持つ矢印の全族を、指定端点を保つ F2 の lift へ渡す。
規約：完全性・随伴・充満忠実性は別の工程。使われ方：Tamme Prop. 10 の両包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxInclusion
end SerrePositivity.KST.LocalizingInvariants.LaxInclusion
namespace SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion
open SerrePositivity.KST.LocalizingInvariants.LaxInclusion

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

def zeroC : D.obj ⟶ C.obj := SSet.const (chosenZeroVertex C.obj).vertex
def zeroD : C.obj ⟶ D.obj := SSet.const (chosenZeroVertex D.obj).vertex

lemma zeroC_post (x : D.obj _⦋0⦌) :
    IsZeroVertex ((zeroC (D := D) ≫ p.hom).app (Opposite.op ⦋0⦌) x) := by
  change IsZeroVertex (p.hom.app _ ((zeroC (D := D)).app _ x))
  apply IsExactFunctor.preservesZero
  rw [zeroC, zeroDiagram_const_vertex]
  exact (chosenZeroVertex C.obj).isZero

lemma zeroD_post (x : C.obj _⦋0⦌) :
    IsZeroVertex ((zeroD (C := C) ≫ q.hom).app (Opposite.op ⦋0⦌) x) := by
  change IsZeroVertex (q.hom.app _ ((zeroD (C := C)).app _ x))
  apply IsExactFunctor.preservesZero
  rw [zeroD, zeroDiagram_const_vertex]
  exact (chosenZeroVertex D.obj).isZero

end SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroC (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxInclusion.zeroC := _root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroC

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxInclusion.zeroC_post := _root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroC_post

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroD (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxInclusion.zeroD := _root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroD

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxInclusion.zeroD_post := _root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroD_post

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxInclusion.zeroC._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroC._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxInclusion.zeroC.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroC.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxInclusion.zeroD.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroD.eq_1
