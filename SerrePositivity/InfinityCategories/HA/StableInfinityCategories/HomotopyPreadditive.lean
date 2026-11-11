module
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
