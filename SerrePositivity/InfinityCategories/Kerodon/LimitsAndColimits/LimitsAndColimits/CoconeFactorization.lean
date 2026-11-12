module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg

/-! # 普遍余錐からの頂点の因子分解

概要：余極限余錐から任意の同じ図式の余錐へ、その全ての脚を保つ頂点の射が存在する。
方針：coslice の始対象性で辺を選び、脚との合成三角形を h C で読む。
規約：この一般の形では一意性は主張しない。使われ方：離散二点図式の二項余積の存在部分。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余極限余錐の頂点から任意の余錐の頂点へ、全ての脚を保つ射が存在する。
方針：余錐の coslice 内の始対象からの辺を頂点に射影する。
規約：値域は quasicategory、形状は任意。使われ方：余積の余錐への射の存在。 -/
lemma exists_coconeVertexFactorization {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    ∃ f : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶
        SSet.HomotopyCategory.mk d.vertex,
      ∀ i : (Δ[0] : SSet.{u}) ⟶ K,
        SSet.Truncated.HomotopyCategory.homMk (c.leg i) ≫ f =
          SSet.Truncated.HomotopyCategory.homMk (d.leg i) := by
  obtain ⟨e⟩ := hc.nonempty_edge d
  exact ⟨SSet.Truncated.HomotopyCategory.homMk
    (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))),
    fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg_comp_projection e i⟩

/-- 概要：同じ一次単体を持つ辺の終点を等号で移すと、そのホモトピー類も同じになる。
方針：終点の等号を除き、辺の構造の等号に帰着する。
規約：quasicategory 性は不要。使われ方：指定された余錐頂点への因子分解。 -/
lemma homMk_comp_eqToHom_of_edge_eq {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (h : y = z) (he : e.edge = f.edge) :
    SSet.Truncated.HomotopyCategory.homMk e ≫
      eqToHom (congrArg (fun a => (SSet.HomotopyCategory.mk a : hoFunctor.obj X)) h) =
        SSet.Truncated.HomotopyCategory.homMk f := by
  subst z
  have hef : e = f := by cases e; cases f; cases he; rfl
  rw [hef, eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
