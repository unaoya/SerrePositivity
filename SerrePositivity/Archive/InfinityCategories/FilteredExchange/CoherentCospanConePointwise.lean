module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationPointTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationCospanCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square

/-!
概要：元の coherent cospan 錐の二全三角形から各点の native な錐を構成する。
方針：元の共通長辺に沿い二三角形を cospan 錐の厳密な pushout で貼る。
規約：底は任意の単体集合、元の二単体を保持。使われ方：各点の引き戻し性の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "L" => coherentTransformationPointDiagram C.leftTriangle.diagram (ULift.up b)
local notation "R" => coherentTransformationPointDiagram C.rightTriangle.diagram (ULift.up b)

/-- 概要：元の二三角形の一点評価の長辺は厳密に共通。
方針：元の長変換の等式をそのまま評価。
規約：長辺を選び直さない。使われ方：native な全錐の貼り合わせ。 -/
lemma coherentCospanConePointwise_common :
    stdSimplex.δ 1 ≫ L = stdSimplex.δ 1 ≫ R := by
  rw [coherentTransformationPointDiagram_long, coherentTransformationPointDiagram_long,
    C.diagonal_eq]

/-- 概要：元の二三角形の評価から貼った各点の全錐。
方針：cospan の錐の二三角形表示の pushout の普遍性。
規約：元の長辺で貼る。使われ方：各点の元の native 錐。 -/
def coherentCospanConePointwiseDiagram :
    join (Δ[0] : SSet.{u + 1}) (horn 2 2 : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  cospanCone_isPushout.desc L R (coherentCospanConePointwise_common F X Y Z C b)

/-- 概要：貼った全錐の左三角形は元の指定左三角形の評価そのもの。
方針：pushout の制限式。規約：全単体の等式。使われ方：元の二次整合の照合。 -/
lemma coherentCospanConePointwiseDiagram_left :
    cospanConeTriangleLeft ≫ coherentCospanConePointwiseDiagram F X Y Z C b = L :=
  cospanCone_isPushout.inl_desc _ _ _

/-- 概要：貼った全錐の右三角形は元の指定右三角形の評価そのもの。
方針：pushout の制限式。規約：全単体の等式。使われ方：元の二次整合の照合。 -/
lemma coherentCospanConePointwiseDiagram_right :
    cospanConeTriangleRight ≫ coherentCospanConePointwiseDiagram F X Y Z C b = R :=
  cospanCone_isPushout.inr_desc _ _ _

/-- 概要：元の三角形から構成した各点の native な cospan 錐。
方針：全錐の cospan への厳密な制限を固定図式とする。
規約：普遍性は仮定しない。使われ方：各点の極限性と fiber 比較の対応。 -/
def coherentCospanConePointwiseCone :
    JoinCone (joinInr Δ[0] (horn 2 2 : SSet.{u + 1}) ≫
      coherentCospanConePointwiseDiagram F X Y Z C b) :=
  ⟨coherentCospanConePointwiseDiagram F X Y Z C b, rfl⟩

end SerrePositivity.InfinityCategories.F2
