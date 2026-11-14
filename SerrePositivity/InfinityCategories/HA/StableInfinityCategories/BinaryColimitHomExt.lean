module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoconeEdgeLift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryColimitDesc
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.ZeroHomotopy

/-! # 二点図式の余極限からの射の一意性

概要：二点図式の余極限の頂点からの射は二つの脚との合成で決まる。
方針：可換な射を余錐間の辺に持ち上げ、coslice の始対象性を使う。
規約：値域は quasicategory。使われ方：h C の二項余積の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：二つの脚と可換な頂点の射は余錐圏の射の射影となる。
方針：射を辺で表し、両脚との可換式から辺を持ち上げる。
規約：値域は quasicategory。使われ方：始対象からの射の一意性の射影。 -/
lemma exists_binaryCoconeHomLift {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (f : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk d.vertex)
    (hL : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ f =
      SSet.Truncated.HomotopyCategory.homMk (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft))
    (hR : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ f =
      SSet.Truncated.HomotopyCategory.homMk (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight)) :
    ∃ E : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) c d,
      SSet.Truncated.HomotopyCategory.homMk
        (E.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))) = f := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective c.vertex d.vertex f
  obtain ⟨E, hE⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_binaryCoconeEdgeLift_of_comm e
    (by rw [he]; exact hL) (by rw [he]; exact hR)
  refine ⟨E, ?_⟩
  have hEq : E.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)) = e :=
    SSet.Truncated.Edge.ext hE
  rw [hEq, he]

/-- 概要：普遍余錐から別の余錐の頂点への射は両脚と可換なら一意。
方針：二つの射を余錐圏へ持ち上げ、始対象性で等しいとする。
規約：二点図式の余極限性のみを使う。使われ方：任意の共通終域での一意性。 -/
lemma binaryColimit_hom_ext_to_cocone {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (f g : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk d.vertex)
    (hfL : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ f =
      SSet.Truncated.HomotopyCategory.homMk (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft))
    (hfR : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ f =
      SSet.Truncated.HomotopyCategory.homMk (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight))
    (hgL : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ g =
      SSet.Truncated.HomotopyCategory.homMk (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft))
    (hgR : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ g =
      SSet.Truncated.HomotopyCategory.homMk (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight)) : f = g := by
  obtain ⟨E, hE⟩ := exists_binaryCoconeHomLift f hfL hfR
  obtain ⟨F, hF⟩ := exists_binaryCoconeHomLift g hgL hgR
  have h := hc.isInitialHo.hom_ext
    (SSet.Truncated.HomotopyCategory.homMk E) (SSet.Truncated.HomotopyCategory.homMk F)
  have hh := congrArg ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)).toFunctor.map) h
  change SSet.Truncated.HomotopyCategory.homMk
    (E.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))) =
    SSet.Truncated.HomotopyCategory.homMk
      (F.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))) at hh
  rwa [hE, hF] at hh

/-- 概要：二点図式の余極限の頂点からの射は両脚との合成で決まる。
方針：共通の合成を辺で表して標的余錐を作り、その頂点へ射を移して比較する。
規約：安定性は不要。使われ方：二項余積の Hom の普遍性。 -/
lemma binaryColimit_hom_ext {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (z : X _⦋0⦌)
    (f g : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk z)
    (hL : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ f =
      SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ g)
    (hR : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ f =
      SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ g) : f = g := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft ≫ p)) z
    (SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ f)
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight ≫ p)) z
    (SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ f)
  let d := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges p a b
  have hd : d.vertex = z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges_vertex p a b
  let w := eqToIso (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj X)) hd)
  have hdL : SSet.Truncated.HomotopyCategory.homMk (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ w.hom =
      SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.homMk_comp_eqToHom_of_edge_eq _ a hd (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges_leg_left p a b)).trans ha
  have hdR : SSet.Truncated.HomotopyCategory.homMk (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ w.hom =
      SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.homMk_comp_eqToHom_of_edge_eq _ b hd (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges_leg_right p a b)).trans hb
  have hfg : f ≫ w.inv = g ≫ w.inv := by
    apply binaryColimit_hom_ext_to_cocone c hc d
    · apply (cancel_mono w.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hdL.symm
    · apply (cancel_mono w.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hdR.symm
    · apply (cancel_mono w.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hL.symm.trans hdL.symm
    · apply (cancel_mono w.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hR.symm.trans hdR.symm
  exact (cancel_mono w.inv).1 hfg

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
