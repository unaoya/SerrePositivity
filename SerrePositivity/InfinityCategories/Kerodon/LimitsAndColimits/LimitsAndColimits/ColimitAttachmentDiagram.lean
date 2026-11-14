module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachment
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentCoconeTransport

/-!
概要：部分図式の余極限頂点を、元の図式へ実際に付加した単体集合と図式を構成する。
方針：部分図式の余錐と元の図式を、join の基底包含に沿う押し出しで貼り合わせる。
規約：形状の単射性・値域の充填性を要求しない。余錐の頂点と元の図式を厳密に保持する。
使われ方：一般の coherent 図式の部分余極限を、余極限対象の span へ組み立てる。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {A C X : SSet.{u}} {p : A ⟶ X}

/-- 部分図式に余極限頂点を付加する実際の形状。 -/
def colimitAttachedShape (i : A ⟶ C) : SSet.{u} :=
  pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u})) i

/-- 元の図式に、指定した部分余錐の頂点と全ての脚を付加した図式。 -/
def colimitAttachedDiagram (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (i : A ⟶ C)
    (F : C ⟶ X) (hi : i ≫ F = p) : colimitAttachedShape i ⟶ X :=
  pushout.desc c.val F (c.property.trans hi.symm)

/-- 付加した余錐上では、その余錐全体を厳密に回収する。 -/
lemma colimitAttachedDiagram_left (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (i : A ⟶ C)
    (F : C ⟶ X) (hi : i ≫ F = p) :
    pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) i ≫ colimitAttachedDiagram c i F hi = c.val :=
  pushout.inl_desc _ _ _

/-- 元の図式上では、元の coherent な写像を厳密に回収する。 -/
lemma colimitAttachedDiagram_right (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (i : A ⟶ C)
    (F : C ⟶ X) (hi : i ≫ F = p) :
    pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) i ≫ colimitAttachedDiagram c i F hi = F :=
  pushout.inr_desc _ _ _

/-- 付加した余極限頂点の、拡張した形状への包含。 -/
def colimitAttachedApex (i : A ⟶ C) : (Δ[0] : SSet.{u}) ⟶ colimitAttachedShape i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) i

/-- 付加した頂点の図式での像は、指定した部分余錐の頂点そのもの。 -/
lemma colimitAttachedApex_diagram (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (i : A ⟶ C)
    (F : C ⟶ X) (hi : i ≫ F = p) :
    colimitAttachedApex i ≫ colimitAttachedDiagram c i F hi =
      SSet.yonedaEquiv.symm c.vertex := by
  rw [colimitAttachedApex, Category.assoc, colimitAttachedDiagram_left, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq,
    Equiv.symm_apply_apply]

/-- 部分余錐が余極限なら、付加後から元の図式への余錐の制限は trivial Kan fibration。 -/
lemma colimitAttachedDiagram_restriction_trivialKanFibration (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (i : A ⟶ C) (F : C ⟶ X) (hi : i ≫ F = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (colimitAttachedDiagram c i F hi)
      (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) i)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceRestriction_trivialKanFibration_of_colimit_attachment c hc i _ _
    (IsPushout.of_hasPushout _ _) _ (colimitAttachedDiagram_left c i F hi)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.2.3.4" (partial := special) "仮定：K 上の図式と、各 K_I に対する指定余極限余錐（Lean が強い：I が一対象一射）。結論：K_F は K と K_I の余錐を貼る押し出しとなり、Lean は双方の制限を満たす図式とその余錐制限の自明 Kan ファイブレーション性を与える（指定した拡張の場合に一致。一般の I と全拡張は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachedDiagram
attribute [cite HTT "4.2.3.4" (partial := special) "仮定：K 上の図式と、各 K_I に対する指定余極限余錐（Lean が強い：I が一対象一射）。結論：K_F は K と K_I の余錐を貼る押し出しとなり、Lean は双方の制限を満たす図式とその余錐制限の自明 Kan ファイブレーション性を与える（指定した拡張の場合に一致。一般の I と全拡張は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachedDiagram_left
attribute [cite HTT "4.2.3.4" (partial := special) "仮定：K 上の図式と、各 K_I に対する指定余極限余錐（Lean が強い：I が一対象一射）。結論：K_F は K と K_I の余錐を貼る押し出しとなり、Lean は双方の制限を満たす図式とその余錐制限の自明 Kan ファイブレーション性を与える（指定した拡張の場合に一致。一般の I と全拡張は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachedDiagram_restriction_trivialKanFibration
attribute [cite HTT "4.2.3.4" (partial := special) "仮定：K 上の図式と、各 K_I に対する指定余極限余錐（Lean が強い：I が一対象一射）。結論：K_F は K と K_I の余錐を貼る押し出しとなり、Lean は双方の制限を満たす図式とその余錐制限の自明 Kan ファイブレーション性を与える（指定した拡張の場合に一致。一般の I と全拡張は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachedDiagram_right
