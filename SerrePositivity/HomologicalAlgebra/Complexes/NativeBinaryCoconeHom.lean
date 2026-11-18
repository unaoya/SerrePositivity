module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoconeEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductCocone

/-!
# Native な二項余錐の指定脚の類

概要：HA 3.2.4.7 の二つの脚を、元の二頂点からのホモトピー圏の射として読む。
方針：脚の始点の標準的な等号で移送する。
規約：余極限性も CAlg の模型も要求しない。
使われ方：テンソル比較の二脚の条件。［一般∞］の移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.NativeBinaryCoconeHom
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 指定二点図式の第一脚を、元の第一頂点からの射として読む。 -/
def binaryCoconeLeftHom {C : SSet.{u}} {x y : C _⦋0⦌}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram x y)) :
    (SSet.HomotopyCategory.mk x : C.HomotopyCategory) ⟶ SSet.HomotopyCategory.mk c.vertex := by
  have h : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram x y) = x := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram, coprod.inl_desc]
    exact SSet.yonedaEquiv.apply_symm_apply x
  exact eqToHom (congrArg SSet.HomotopyCategory.mk h.symm) ≫
    SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft)

/-- 指定二点図式の第二脚を、元の第二頂点からの射として読む。 -/
def binaryCoconeRightHom {C : SSet.{u}} {x y : C _⦋0⦌}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram x y)) :
    (SSet.HomotopyCategory.mk y : C.HomotopyCategory) ⟶ SSet.HomotopyCategory.mk c.vertex := by
  have h : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram x y) = y := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram, coprod.inr_desc]
    exact SSet.yonedaEquiv.apply_symm_apply y
  exact eqToHom (congrArg SSet.HomotopyCategory.mk h.symm) ≫
    SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight)

end SerrePositivity.NativeBinaryCoconeHom
