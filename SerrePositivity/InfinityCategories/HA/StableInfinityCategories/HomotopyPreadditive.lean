module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyAdditiveInverse
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.Group.MinimalAxioms

/-! # 安定 ∞ 圏のホモトピー圏の前加法構造

概要：h C の射の双積による加法に逆元を加え、前加法圏の instance を構成する。
方針：全射の加法左逆元を選んで可換群とし、双積の加法の合成との分配則を使う。
規約：零射と既存の双積を保持。使われ方：整数シフトの加法性と三角構造。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

attribute [local instance] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomAddCommMonoid

/-- 概要：安定な quasicategory の各 Hom の可換モノイドは可換群となる。
方針：証明済みの加法左逆元を古典的に選び、群の最小公理を満たす。
規約：加法と零は双積の可換モノイドのもの。使われ方：前加法構造の homGroup。 -/
@[instance_reducible]
def stableHomAddCommGroup {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (A B : hoFunctor.obj X) : AddCommGroup (A ⟶ B) := by
  let : Neg (A ⟶ B) := ⟨fun f => Classical.choose (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_stableHom_additiveInverse f)⟩
  let G : AddGroup (A ⟶ B) := AddGroup.ofLeftAxioms add_assoc zero_add
    (fun f => Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_stableHom_additiveInverse f))
  exact { G, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomAddCommMonoid A B with }

/-- 概要：安定な quasicategory のホモトピー圏は前加法圏である。
方針：双積由来の Hom の可換群と、合成の二つの分配則を束ねる。
規約：安定性以外の加法性は前提にしない。使われ方：Pretriangulated の構成。 -/
instance preadditive_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    Preadditive (hoFunctor.obj X) where
  homGroup := stableHomAddCommGroup
  add_comp _ _ _ := SemiadditiveOfBinaryBiproducts.add_comp
  comp_add _ _ _ := SemiadditiveOfBinaryBiproducts.comp_add

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.2.9" (partial := stronger-hyp) "仮定：安定準圏 X（Lean は IsStable で仮定をまとめる。HA は点付き性・余ファイバー・懸垂同値で述べる）。結論：hX の前加法構造と有限双積（一致）。HA の仮定から IsStable への直接の比較宣言は採用した型にない。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho
attribute [cite HA "1.4.1.3" (partial := component) "仮定：安定準圏（Lean が弱い：presentable 性は不要）。結論：ホモトピー圏の前加法性と双積があり、原典冒頭の加法性に対応する（Lean が弱い：各対象の余群構造と compactly generated な場合の Brown の全仮定の確認は含まれない）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho
attribute [cite HA "6.1.6.17" (partial := component) "仮定：安定な準圏 C（HA と一致）。結論：hC は前加法圏で全有限双積を持つ（本文で明記された hC の additive 性に一致する部分）。C の全相対 norm の可逆性を束ねる semiadditive 述語への比較は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho
