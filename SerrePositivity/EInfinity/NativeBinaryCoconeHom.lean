module

public import SerrePositivity.InfinityCategories.Stable.BinaryCoconeEdges
public import SerrePositivity.InfinityCategories.Stable.BinaryCoproductCocone

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
namespace SerrePositivity.EInfinity
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 指定二点図式の第一脚を、元の第一頂点からの射として読む。 -/
def binaryCoconeLeftHom {C : SSet.{u}} {x y : C _⦋0⦌}
    (c : JoinCocone (binaryPointDiagram x y)) :
    (SSet.HomotopyCategory.mk x : C.HomotopyCategory) ⟶ SSet.HomotopyCategory.mk c.vertex := by
  have h : SSet.yonedaEquiv (binaryPointLeft ≫ binaryPointDiagram x y) = x := by
    rw [binaryPointLeft, binaryPointDiagram, coprod.inl_desc]
    exact SSet.yonedaEquiv.apply_symm_apply x
  exact eqToHom (congrArg SSet.HomotopyCategory.mk h.symm) ≫
    SSet.Truncated.HomotopyCategory.homMk (c.leg binaryPointLeft)

/-- 指定二点図式の第二脚を、元の第二頂点からの射として読む。 -/
def binaryCoconeRightHom {C : SSet.{u}} {x y : C _⦋0⦌}
    (c : JoinCocone (binaryPointDiagram x y)) :
    (SSet.HomotopyCategory.mk y : C.HomotopyCategory) ⟶ SSet.HomotopyCategory.mk c.vertex := by
  have h : SSet.yonedaEquiv (binaryPointRight ≫ binaryPointDiagram x y) = y := by
    rw [binaryPointRight, binaryPointDiagram, coprod.inr_desc]
    exact SSet.yonedaEquiv.apply_symm_apply y
  exact eqToHom (congrArg SSet.HomotopyCategory.mk h.symm) ≫
    SSet.Truncated.HomotopyCategory.homMk (c.leg binaryPointRight)

end SerrePositivity.EInfinity
