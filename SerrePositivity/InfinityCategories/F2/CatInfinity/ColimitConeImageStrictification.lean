module

public import SerrePositivity.InfinityCategories.F1B.Cones.CoconeFamilyEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexIsoLifting
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeFamily

/-!
概要：余極限錐の像を同じ図式上の指定余極限錐へ厳密に合わせる。
方針：図式固定の余錐族の始対象の同型を、後合成の同値持ち上げで戻す。
規約：元の図式は全次数で固定し、像の全余錐の射を厳密に保つ。
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

/-- 概要：像も余極限である余極限錐を、像が指定余極限錐そのものとなるよう取り直せる。
方針：余錐族の二つの始対象の同型を持ち上げ、元の始対象性を移送する。
規約：取り直した余錐も元の図式 r 上にある。
使われ方：lax pullback の錐の存在を両入力を固定して証明する。 -/
lemma exists_colimitCone_with_specified_image {J X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y)
    (hf : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting f) {r : J ⟶ X}
    (c₀ : JoinCocone r) (hc₀ : IsColimitCone c₀)
    (hc₀f : IsColimitCone (F1B.kanPostcomposeCocone f c₀))
    (d : JoinCocone (r ≫ f)) (hd : IsColimitCone d) :
    ∃ c : JoinCocone r, IsColimitCone c ∧ F1B.kanPostcomposeCocone f c = d := by
  let x := coconeFamilyVertexEquiv r c₀
  let y := coconeFamilyVertexEquiv (r ≫ f) d
  have hx : IsInitialVertex x := (isColimitCone_iff_isInitialVertex_coconeFamily c₀).1 hc₀
  have hy : IsInitialVertex y := (isColimitCone_iff_isInitialVertex_coconeFamily d).1 hd
  have hfx : IsInitialVertex ((F1B.kanCoconeFamilyPostcomp r f).app (Opposite.op ⦋0⦌) x) := by
    dsimp only [x]
    rw [F1B.kanCoconeFamilyPostcomp_vertex]
    exact (isColimitCone_iff_isInitialVertex_coconeFamily _).1 hc₀f
  obtain ⟨z, hz, ⟨ez⟩⟩ := F1B.exists_kanVertexIso_lift_target
    (F1B.kanCoconeFamilyPostcomp r f) (SerrePositivity.InfinityCategories.F1B.coconeFamilyPostcomp_equivalenceLifting r f hf)
    x y (initialVertexIso hy hfx)
  let c := (coconeFamilyVertexEquiv r).symm z
  have hcz : coconeFamilyVertexEquiv r c = z := (coconeFamilyVertexEquiv r).apply_symm_apply z
  refine ⟨c, ?_, ?_⟩
  · apply (isColimitCone_iff_isInitialVertex_coconeFamily c).2
    rw [hcz]
    exact hx.of_vertexIso ez.symm
  · apply (coconeFamilyVertexEquiv (r ≫ f)).injective
    rw [← F1B.kanCoconeFamilyPostcomp_vertex, hcz]
    exact hz

end SerrePositivity.InfinityCategories.F2
