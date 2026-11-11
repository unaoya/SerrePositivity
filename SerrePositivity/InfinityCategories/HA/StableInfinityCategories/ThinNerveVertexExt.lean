module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinVertexSummands
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.PastingRightCocone

/-!
概要：thin な nerve への射と余錐を実頂点で比較する。
方針：元の射影・実余錐・全単体の頂点式を保持して比較する。
規約：一般安定性の結論は先取りしない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

lemma thinNerveHom_ext_of_vertices {A : SSet.{u}} {P : Type u} [SmallCategory P]
    [Quiver.IsThin P] (F G : A ⟶ nerve P)
    (h : ∀ v : A _⦋0⦌, nerveEquiv (F.app (Opposite.op ⦋0⦌) v) =
      nerveEquiv (G.app (Opposite.op ⦋0⦌) v)) : F = G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  let α := (SimplexCategory.const ⦋0⦌ n.unop i).op
  have hf := congrArg nerveEquiv (ConcreteCategory.congr_hom (F.naturality α) s)
  have hg := congrArg nerveEquiv (ConcreteCategory.congr_hom (G.naturality α) s)
  exact hf.symm.trans ((h (A.map α s)).trans hg)

lemma thinNerveCocone_val_eq_of_vertex {K : SSet.{u}} {P : Type u} [SmallCategory P]
    [Quiver.IsThin P] {p : K ⟶ nerve P} (c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (h : c.vertex = d.vertex) : c.val = d.val := by
  apply thinNerveHom_ext_of_vertices
  intro v
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinVertexSummands v with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · have hc := ConcreteCategory.congr_hom (NatTrans.congr_app c.property
      (Opposite.op ⦋0⦌)) a
    have hd := ConcreteCategory.congr_hom (NatTrans.congr_app d.property
      (Opposite.op ⦋0⦌)) a
    exact congrArg nerveEquiv (hc.trans hd.symm)
  · have hb : b = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) :=
      stdSimplex.obj₀Equiv.injective (by apply Fin.ext; omega)
    subst b
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq] at h
    change nerveEquiv (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]) ≫ c.val).app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) =
      nerveEquiv (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]) ≫ d.val).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))
    rw [← SSet.yonedaEquiv_comp, ← SSet.yonedaEquiv_comp,
      Category.id_comp, Category.id_comp]
    exact congrArg nerveEquiv h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
