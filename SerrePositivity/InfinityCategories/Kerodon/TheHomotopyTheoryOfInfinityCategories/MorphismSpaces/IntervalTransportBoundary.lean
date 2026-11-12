module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalTransportCylinder
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CylinderSquareEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointMaps

/-!
概要：区間上の輸送円柱の両端図式と元の全空間の両端との厳密な比較。
方針：二つの fiber を次数ごとの直和にまとめ、実際の比較の両端を計算する。
規約：元の全空間の射影の充填性は端点の単射性に不要。
使われ方：端点写像を固定した相対関手空間への円柱比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間上の射の二つの fiber を全空間へ同時に含める。
方針：二つの fiber の包含を両端図式でまとめる。
規約：全ての次数で二つの fiber は交わらない。
使われ方：元の全空間上の端点写像を厳密に固定する制限。 -/
def intervalFiberEndpointInclusion {E : SSet.{u}} (p : E ⟶ (Δ[1] : SSet.{u})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _)

/-- 概要：区間の両端 fiber をまとめた包含は単射。
方針：同じ fiber では部分型の値を回収し、異なる fiber では時刻が異なることを使う。
規約：p の fibration 性は要求しない。
使われ方：両端への相対関手空間の制限の left fibration 性。 -/
instance intervalFiberEndpointInclusion_mono {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) : Mono (intervalFiberEndpointInclusion p) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b => exact congrArg Sum.inl (Subtype.ext h)
    | inr b =>
      have hq := a.property.symm.trans ((congrArg (p.app _) h).trans b.property)
      have ht := congrArg (fun z : (Δ[1] : SSet.{u}) _⦋n⦌ ↦ z 0) hq
      change (0 : Fin 2) = 1 at ht
      exact (Fin.zero_ne_one ht).elim
  | inr a =>
    cases y with
    | inl b =>
      have hq := b.property.symm.trans ((congrArg (p.app _) h.symm).trans a.property)
      have ht := congrArg (fun z : (Δ[1] : SSet.{u}) _⦋n⦌ ↦ z 0) hq
      change (0 : Fin 2) = 1 at ht
      exact (Fin.zero_ne_one ht).elim
    | inr b => exact congrArg Sum.inr (Subtype.ext h)

/-- 概要：写像円柱の始点と終点を同時に含める図式。
方針：円柱の始点と pushout の終点部分を両端図式にまとめる。
規約：f は任意の射。
使われ方：円柱側の端点条件を固定する制限。 -/
def transportCylinderEndpointInclusion {K J : SSet.{u}} (f : K ⟶ J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram K J ⟶ pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderSquareSourceInclusion f) (pushout.inr _ _)

/-- 概要：輸送円柱から全空間への実際の比較は両端の包含を厳密に保つ。
方針：二つの端点で pushout の desc の公式を計算する。
規約：始点の輸送条件と終点の貼り合わせ条件を使う。
使われ方：端点固定の比較の単射性と底の可換性。 -/
lemma transportCylinderEndpointInclusion_comparison {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (H : Δ[1] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    transportCylinderEndpointInclusion f ≫
        pushout.desc H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h₁ =
      intervalFiberEndpointInclusion p := by
  apply SSet.hom_ext
  intro n
  ext x
  cases x with
  | inl a =>
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderSquareSourceInclusion f ≫ pushout.desc H _ h₁).app n) a = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderSquareSourceInclusion, Category.assoc, pushout.inl_desc, h₀]
    rfl
  | inr a =>
    change ((pushout.inr _ _ ≫ pushout.desc H _ h₁).app n) a = _
    rw [pushout.inr_desc]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
