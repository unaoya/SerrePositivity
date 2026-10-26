module

public import SerrePositivity.KST.LocalizingInvariants.CoreFlag.EquivalenceDiagrams
public import SerrePositivity.KST.LocalizingInvariants.CoreFlag.SimplexContraction
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
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories

/-- 標準単体の全辺を反転する図式への定数包含は圏同値。 -/
lemma simplexConstant_isQCatEquivalence (C : SSet.{u}) [Quasicategory C] (m : ℕ) :
    IsQCatEquivalence (constant (Δ[m] : SSet.{u}) C) :=
  constant_isQCatEquivalence _ (initialContraction m)

/-- 同じ元の定数包含は弱ホモトピー同値。 -/
lemma simplexConstant_isWeakHomotopyEquivalence (C : SSet.{u}) [Quasicategory C] (m : ℕ) :
    IsWeakHomotopyEquivalence (constant (Δ[m] : SSet.{u}) C) :=
  (simplexConstant_isQCatEquivalence C m).isWeakHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants.CoreFlag
