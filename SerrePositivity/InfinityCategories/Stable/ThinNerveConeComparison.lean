module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCoreSourceCone
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagramEvaluation

/-!
概要：元の pullback 錐を穿孔 core へ延長し、外側の錐と実比較辺を作る。
方針：同じ native 錐の厳密な制限と頂点を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ と合成式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma thinNerveCone_val_eq_of_vertex {K : SSet.{u}} {P : Type u} [SmallCategory P]
    [Quiver.IsThin P] {p q : K ⟶ nerve P} (c : JoinCone p) (d : JoinCone q)
    (hpq : p = q) (h : c.vertex = d.vertex) : c.val = d.val := by
  subst q
  apply thinNerveHom_ext_of_vertices
  intro v
  rcases HomotopyLimits.joinVertexSummands v with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · have ha : a = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) :=
      stdSimplex.obj₀Equiv.injective (by apply Fin.ext; omega)
    subst a
    rw [JoinCone.vertex_eq, JoinCone.vertex_eq] at h
    change nerveEquiv ((joinInl Δ[0] K ≫ c.val).app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) =
      nerveEquiv ((joinInl Δ[0] K ≫ d.val).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))
    rw [← SSet.yonedaEquiv_comp, ← SSet.yonedaEquiv_comp,
      Category.id_comp, Category.id_comp]
    exact congrArg nerveEquiv h
  · have hc := ConcreteCategory.congr_hom (NatTrans.congr_app c.property
      (Opposite.op ⦋0⦌)) b
    have hd := ConcreteCategory.congr_hom (NatTrans.congr_app d.property
      (Opposite.op ⦋0⦌)) b
    exact congrArg nerveEquiv (hc.trans hd.symm)

end SerrePositivity.InfinityCategories
