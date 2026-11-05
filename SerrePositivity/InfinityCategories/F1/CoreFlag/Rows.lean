module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.F1.CoreFlag.EquivalenceDiagrams
public import SerrePositivity.InfinityCategories.F1.CoreFlag.SimplexContraction
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy

/-!
概要：全辺可逆な標準単体図式への定数包含の圏同値と弱同値。
方針：初頂点で評価し、標準単体の指定された収縮を使う。
規約：core を取る前の関手圏の全部分圏を対象とする。
使われ方：Sp-8 の転置した各行の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
end SerrePositivity.KST.LocalizingInvariants.CoreFlag
namespace SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag
open SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories

/-- 標準単体の全辺を反転する図式への定数包含は圏同値。 -/
lemma simplexConstant_isQCatEquivalence (C : SSet.{u}) [Quasicategory C] (m : ℕ) :
    IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant (Δ[m] : SSet.{u}) C) :=
  _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant_isQCatEquivalence _ (_root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.initialContraction m)

/-- 同じ元の定数包含は弱ホモトピー同値。 -/
lemma simplexConstant_isWeakHomotopyEquivalence (C : SSet.{u}) [Quasicategory C] (m : ℕ) :
    IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant (Δ[m] : SSet.{u}) C) :=
  (_root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.simplexConstant_isQCatEquivalence C m).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.simplexConstant_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.simplexConstant_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.simplexConstant_isWeakHomotopyEquivalence := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.simplexConstant_isWeakHomotopyEquivalence
