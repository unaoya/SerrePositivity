module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseStabilityDescent
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseZeroTriangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure

/-! # 指定頂点の実安定閉包の宇宙不変性

概要：ULift に沿う指定頂点の実安定閉包への所属は保存・反映される。
方針：実零性・同型・全四角形の普遍性を、閉包の生成手順の帰納で持ち上げ・降下する。
規約：安定性自体は仮定しない。使われ方：有限 cell の実分母条件の native 宇宙への降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X]

/-- 実安定閉包の全生成手順を宇宙持ち上げできる。 -/
lemma StableVertexClosure.ulift (P : Set (X _⦋0⦌)) {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up '' P)
      (ULift.up x) := by
  induction hx with
  | of_mem hx => exact .of_mem ⟨_, hx, rfl⟩
  | of_zero hx => exact .of_zero ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _).mp hx)
  | of_iso e _ ih => exact .of_iso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.uliftVertexIso e) ih
  | of_cofiber t ht _ _ ih₀ ih₁ =>
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_cofiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle.ulift.{u, v} t)
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPushoutSquare_iff_ulift t.square).mp ht) ih₀ ih₁
  | of_fiber t ht _ _ ih₁ ih₂ =>
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_fiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle.ulift.{u, v} t)
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPullbackSquare_iff_ulift t.square).mp ht) ih₁ ih₂

/-- 任意の持ち上げた頂点の実安定閉包の生成手順を元の宇宙へ降ろせる。 -/
lemma StableVertexClosure.down (P : Set (X _⦋0⦌))
    {x : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (ULift.up '' P) x) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x.down := by
  induction hx with
  | of_mem hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact .of_mem hy
  | of_zero hx => exact .of_zero ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _).mpr hx)
  | of_iso e _ ih => exact .of_iso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downVertexIso e) ih
  | of_cofiber t ht _ _ ih₀ ih₁ =>
    have h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.down.square 0 0) :=
      (t.down_vertex 0 0).symm ▸ ih₀
    have h₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.down.square 1 0) :=
      (t.down_vertex 1 0).symm ▸ ih₁
    exact (t.down_vertex 1 1) ▸
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_cofiber t.down (t.isCofiber_down ht) h₀ h₁
  | of_fiber t ht _ _ ih₁ ih₂ =>
    have h₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.down.square 1 0) :=
      (t.down_vertex 1 0).symm ▸ ih₁
    have h₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.down.square 1 1) :=
      (t.down_vertex 1 1).symm ▸ ih₂
    exact (t.down_vertex 0 0) ▸
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_fiber t.down (t.isFiber_down ht) h₁ h₂

/-- 指定実頂点の安定閉包への所属は宇宙持ち上げで変わらない。 -/
theorem stableVertexClosure_ulift_iff (P : Set (X _⦋0⦌)) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up '' P)
      (ULift.up x) ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x :=
  ⟨fun hx => hx.down P, fun hx => hx.ulift P⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
