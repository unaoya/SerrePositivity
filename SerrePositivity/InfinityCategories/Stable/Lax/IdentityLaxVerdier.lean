module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import SerrePositivity.InfinityCategories.F1B.Adjunction.Adjunction
public import SerrePositivity.InfinityCategories.Stable.Verdier.StableCategories

/-!
分割で生成：docstring を書き直すこと
概要：恒等矢印の対角・恒等 lax 圏・cofiber 差は実 Verdier 列をなす。
方針：元の対角の充満忠実性と真の核を、差の実右随伴からの局所化に接続する。
規約：Q の安定性だけを入力する。使われ方：一般商の列を比較する普遍の列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.IdentityLax
end SerrePositivity.KST.LocalizingInvariants.IdentityLax
namespace SerrePositivity.InfinityCategories.Stable.Lax.IdentityLax
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.IdentityLax
variable (Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u})

def identityAdjunction : QCatAdjunction (𝟙 Q.obj) (𝟙 Q.obj) :=
  Bicategory.Adjunction.id (qcatOf Q.obj)

end SerrePositivity.InfinityCategories.Stable.Lax.IdentityLax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Lax.IdentityLax.identityAdjunction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IdentityLax.identityAdjunction := _root_.SerrePositivity.InfinityCategories.Stable.Lax.IdentityLax.identityAdjunction
