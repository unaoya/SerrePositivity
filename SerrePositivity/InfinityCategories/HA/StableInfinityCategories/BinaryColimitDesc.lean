module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoconeEdges
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFactorization

/-! # 二点図式の余極限からの射の存在

概要：離散二点図式の余極限の頂点から、指定された二本の脚を延長する h C の射が存在する。
方針：二本の射を辺で表して余錐を作り、普遍余錐からの射をその頂点へ射影する。
規約：一意性は別途証明する。使われ方：h C の二項余積の存在部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：二点図式の余極限から、指定された二本の射を延長する射が存在する。
方針：辺の表示から任意の余錐を構成し、余極限の因子分解を終点の等号で指定終域へ移す。
規約：X は quasicategory、安定性自体は不要。使われ方：二項余積の降下射。 -/
lemma exists_binaryColimit_desc {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (z : X _⦋0⦌)
    (u : (SSet.HomotopyCategory.mk (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft ≫ p)) : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk z)
    (v : (SSet.HomotopyCategory.mk (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight ≫ p)) : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk z) :
    ∃ f : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk z,
      SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ f = u ∧
        SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ f = v := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft ≫ p)) z u
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight ≫ p)) z v
  let d := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges p a b
  have hd : d.vertex = z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges_vertex p a b
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_coconeVertexFactorization c hc d
  let e := eqToHom (congrArg (fun a => (SSet.HomotopyCategory.mk a : hoFunctor.obj X)) hd)
  refine ⟨f ≫ e, ?_, ?_⟩
  · rw [← Category.assoc, hf _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.homMk_comp_eqToHom_of_edge_eq (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) a hd
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges_leg_left p a b)).trans ha
  · rw [← Category.assoc, hf _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.homMk_comp_eqToHom_of_edge_eq (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) b hd
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges_leg_right p a b)).trans hb

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
