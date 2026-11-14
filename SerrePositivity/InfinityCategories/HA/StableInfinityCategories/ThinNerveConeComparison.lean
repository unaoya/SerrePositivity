module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreSourceCone
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FiniteShapes
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramEvaluation

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma thinNerveCone_val_eq_of_vertex {K : SSet.{u}} {P : Type u} [SmallCategory P]
    [Quiver.IsThin P] {p q : K ⟶ nerve P} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q)
    (hpq : p = q) (h : c.vertex = d.vertex) : c.val = d.val := by
  subst q
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinVertexSummands v with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · have ha : a = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) :=
      stdSimplex.obj₀Equiv.injective (by apply Fin.ext; omega)
    subst a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq] at h
    change nerveEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ c.val).app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) =
      nerveEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ d.val).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))
    rw [← SSet.yonedaEquiv_comp, ← SSet.yonedaEquiv_comp,
      Category.id_comp, Category.id_comp]
    exact congrArg nerveEquiv h
  · have hc := ConcreteCategory.congr_hom (NatTrans.congr_app c.property
      (Opposite.op ⦋0⦌)) b
    have hd := ConcreteCategory.congr_hom (NatTrans.congr_app d.property
      (Opposite.op ⦋0⦌)) b
    exact congrArg nerveEquiv (hc.trans hd.symm)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
