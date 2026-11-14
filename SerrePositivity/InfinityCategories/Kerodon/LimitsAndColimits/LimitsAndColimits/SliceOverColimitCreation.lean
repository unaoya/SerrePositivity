module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SliceOverCoconeProjection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SliceOverCoconeFromColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.InitialObjectsInSlices
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeOpposite

/-!
概要：対象上の余極限を元の圏の指定余極限から構成し、射影で検出する。
方針：二重 slice の全同型で、底の余錐の始対象性を元の対象上へ移す。
規約：元の対象への射と指定した全余錐の射影を厳密に保持する。
使われ方：compact 表示を元の対象の上で同期する余極限操作。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：対象上の余錐の底が余極限なら、その元の余錐も余極限。
方針：二重 slice の同型で、始対象を始域とする射の始対象性へ帰着する。
規約：元の全余錐を選び直さない。
使われ方：対象上の colimit の存在と射影の保存。 -/
lemma sliceOver_isColimitCone_of_projection {K X : SSet.{u}} [Quasicategory X]
    (x : (Δ[0] : SSet.{u}) ⟶ X) {a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone a)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceOverCoconeIso x a).hom c).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isInitialVertex_sliceOver_of_source (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceOverAugmentationCocone x a)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceOverCoconeForward x a).app (Opposite.op ⦋0⦌) c)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceOverCoconeForward_vertex_projection]
  exact hc

/-- 概要：底の指定全余極限余錐を射影とする対象上の全余極限余錐がある。
方針：対象上の余錐を構成し、射影による余極限性の検出を適用する。
規約：底の全射を厳密に回収する。
使われ方：元の対象上での表示と余極限の同期。 -/
lemma exists_sliceOver_colimitCone_with_projection {K X : SSet.{u}} [Quasicategory X]
    (x : (Δ[0] : SSet.{u}) ⟶ X) (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone a, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ d.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x = c.val := by
  obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sliceOver_cocone_lifting_colimit x a c hc
  refine ⟨d, sliceOver_isColimitCone_of_projection x d ?_, hd⟩
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) d = c := Subtype.ext hd
  exact he.symm ▸ hc

/-- 概要：底の全図式が余極限を持てば対象上の元の全図式も余極限を持つ。
方針：指定した底の余極限を同じ対象上へ持ち上げる。
規約：全余完備性への強化を要求しない。
使われ方：任意小形状と指定された filtered 形状の両方に使う。 -/
lemma sliceOver_hasColimit_of_projection {K X : SSet.{u}} [Quasicategory X]
    (x : (Δ[0] : SSet.{u}) ⟶ X) (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit a := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd, _⟩ := exists_sliceOver_colimitCone_with_projection x a c hc
  exact ⟨d, hd⟩

/-- 概要：底に余極限があれば、元の対象上の余錐の余極限性は射影で保たれ検出される。
方針：底から構成した余極限と元の余極限の一意同型を射影へ送る。
規約：同じ全余錐を判定する。
使われ方：対象上の射影の小余極限・filtered 余極限保存。 -/
lemma sliceOver_isColimitCone_iff_projection {K X : SSet.{u}} [Quasicategory X]
    (x : (Δ[0] : SSet.{u}) ⟶ X) {a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) c) := by
  constructor
  · intro hc
    obtain ⟨b, hb⟩ := h
    obtain ⟨d, hd, hdb⟩ := exists_sliceOver_colimitCone_with_projection x a b hb
    have hd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) d) :=
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) d = b from Subtype.ext hdb).symm ▸ hb
    exact hd'.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d c hd hc)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)))
  · exact sliceOver_isColimitCone_of_projection x c

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.13.8" (partial := special) "仮定：準圏 C と図式 p（Lean が強い：スライスを定める q の始域 T が一点）。結論：底の余極限余錐を厳密に持ち上げ、与えた余錐が余極限かを射影で検出する（Lean が弱い：任意の T のスライスは含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_sliceOver_colimitCone_with_projection
attribute [cite HTT "1.2.13.8" (partial := special) "仮定：準圏 C と図式 p（Lean が強い：スライスを定める q の始域 T が一点）。結論：底の余極限余錐を厳密に持ち上げ、与えた余錐が余極限かを射影で検出する（Lean が弱い：任意の T のスライスは含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOver_isColimitCone_iff_projection
