module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeFamilyPostcompLifting
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexIsoLifting
public import SerrePositivity.InfinityCategories.Core.LimitConeFamily

/-!
概要：極限錐の像を同じ図式上の指定極限錐へ厳密に合わせる。
方針：図式固定の錐族の終対象の同型を、後合成の同値持ち上げで戻す。
規約：元の図式は全次数で固定し、像の全錐の射を厳密に保つ。
使われ方：選んだ両入力の錐に矢印圏の錐を合わせる存在構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：像も極限である極限錐を、像が指定極限錐そのものとなるよう取り直せる。
方針：錐族の二つの終対象の同型を持ち上げ、元の終対象性を移送する。
規約：取り直した錐も元の図式 r 上にある。
使われ方：lax pullback の錐の存在を両入力を固定して証明する。 -/
lemma exists_limitCone_with_specified_image {J X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y)
    (hf : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting f) {r : J ⟶ X}
    (c₀ : JoinCone r) (hc₀ : IsLimitCone c₀) (hc₀f : IsLimitCone (mapJoinCone f c₀))
    (d : JoinCone (r ≫ f)) (hd : IsLimitCone d) :
    ∃ c : JoinCone r, IsLimitCone c ∧ mapJoinCone f c = d := by
  let x := coneFamilyVertexEquiv r c₀
  let y := coneFamilyVertexEquiv (r ≫ f) d
  have hx : IsTerminalVertex x := (isLimitCone_iff_isTerminalVertex_coneFamily c₀).1 hc₀
  have hy : IsTerminalVertex y := (isLimitCone_iff_isTerminalVertex_coneFamily d).1 hd
  have hfx : IsTerminalVertex ((coneFamilyPostcomp r f).app (Opposite.op ⦋0⦌) x) := by
    dsimp only [x]
    rw [coneFamilyPostcomp_vertex]
    exact (isLimitCone_iff_isTerminalVertex_coneFamily _).1 hc₀f
  obtain ⟨z, hz, ⟨ez⟩⟩ := F1B.exists_kanVertexIso_lift_target
    (coneFamilyPostcomp r f) (coneFamilyPostcomp_equivalenceLifting r f hf)
    x y (terminalVertexIso hy hfx)
  let c := (coneFamilyVertexEquiv r).symm z
  have hcz : coneFamilyVertexEquiv r c = z := (coneFamilyVertexEquiv r).apply_symm_apply z
  refine ⟨c, ?_, ?_⟩
  · apply (isLimitCone_iff_isTerminalVertex_coneFamily c).2
    rw [hcz]
    exact hx.of_vertexIso ez.symm
  · apply (coneFamilyVertexEquiv (r ≫ f)).injective
    rw [← coneFamilyPostcomp_vertex, hcz]
    exact hz

end SerrePositivity.InfinityCategories.F2
