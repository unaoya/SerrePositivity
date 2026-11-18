module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LimitConeVertexTransport

/-!
概要：left cofinal な制限の極限錐から、同じ頂点の元の全極限錐と指定比較同値を作る。
方針：極限の存在を回収し、制限錐の頂点比較で頂点を運び、同じ錐圏内の同値を固定する。
使われ方：HTT 4.1.3.1、Kerodon §7.2（Tag 02MZ）の Čech 極限の回収。
規約：制限の厳密な等号は要求しない。頂点は等号、錐の比較は指定同値で保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 同じ頂点の元の全錐と、制限後の錐から指定錐への実際の同値。
制限の厳密な等号は要求しない。 -/
structure CofinalLimitLiftData {A B X : SSet.{u}} (f : A ⟶ B) (F : B ⟶ X)
    (t : JoinCone (f ≫ F)) where
  cone : JoinCone F
  isLimit : IsLimitCone cone
  vertex_eq : cone.vertex = t.vertex
  comparison : VertexIso (X := sliceOver (f ≫ F)) (restrictJoinCone cone f) t

/-- left cofinal な制限から、頂点を厳密に保つ全錐と指定比較同値を構成する。
制限の厳密な等号は要求しない。 -/
def specifiedCofinalLimitLift {A B X : SSet.{u}} [Quasicategory B] [Quasicategory X]
    (f : A ⟶ B) (hf : IsLeftCofinal f) (F : B ⟶ X)
    (t : JoinCone (f ≫ F)) (ht : IsLimitCone t) : CofinalLimitLiftData f F t := by
  apply Classical.choice
  obtain ⟨c, hc⟩ := hasLimit_of_leftCofinal f hf F ⟨t, ht⟩
  have hcr := (isLimitCone_iff_restrict_of_leftCofinal f hf F c).mp hc
  let i : VertexIso t.vertex c.vertex :=
    (limitVertexIso (restrictJoinCone c f) t hcr ht).symm ≪≫
      eqToIso (congrArg HomotopyCategory.mk (restrictJoinCone_vertex c f))
  obtain ⟨e, he⟩ := homotopyCategory_homMk_surjective _ _ i.hom
  have hei : IsInvertibleEdge e := by
    change IsIso (Truncated.HomotopyCategory.homMk e)
    rw [he]
    infer_instance
  obtain ⟨d, hd, hv⟩ :=
    SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_limitCone_vertex_of_invertible
      c hc (⟨e.edge, e.src_eq, e.tgt_eq⟩ : X.Edge t.vertex c.vertex) hei
  exact ⟨⟨d, hd, hv,
    limitConeIso (restrictJoinCone d f) t
      ((isLimitCone_iff_restrict_of_leftCofinal f hf F d).mp hd) ht⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
