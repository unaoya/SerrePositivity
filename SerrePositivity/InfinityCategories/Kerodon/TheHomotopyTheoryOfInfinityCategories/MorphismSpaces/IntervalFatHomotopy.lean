module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFatDiagram

/-!
概要：両端を固定した fat join 図式のホモトピーを区間模型の族へ移す。
方針：円柱へ制限した二重区間の図式を、両端固定の内部 Hom に curry する。
規約：ホモトピーの区間はパラメータの第二因子。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、写像空間の比較の逆向きの族の回収。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：両端を固定する二重区間の図式は区間模型への二つの族のホモトピー。
方針：区間の片方に関して curry し、もう片方の端点の式を普遍性で確認する。
規約：第一の区間は写像の始域、最後の区間はホモトピーの時間。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定端点の図式から族のホモトピーへの移行。 -/
noncomputable def intervalMappingHomotopyOfSquare {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (K : Δ[1] ⊗ (A ⊗ Δ[1]) ⟶ X)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A ⊗ Δ[1]) ≫ K = SSet.const x)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A ⊗ Δ[1]) ≫ K = SSet.const y)
    (h₀ : (Δ[1] ◁ (SSet.ι₀ : A ⟶ A ⊗ Δ[1])) ≫ K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f)
    (h₁ : (Δ[1] ◁ (SSet.ι₁ : A ⟶ A ⊗ Δ[1])) ≫ K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g) :
    SSet.Homotopy f g where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints K hx hy
  h₀ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints]
    exact h₀
  h₁ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints]
    exact h₁
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：両端を固定する fat join 図式のホモトピーを区間模型のホモトピーへ移す。
方針：円柱に制限し、零単体の因子を補い、二重区間の図式を curry する。
規約：左右の固定条件を全ホモトピー時間について明示する。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、fat join の同型から区間模型の族の同型への移行。 -/
noncomputable def intervalMappingHomotopyOfFatJoin {A X : SSet.{u}} {x y : X _⦋0⦌}
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A (Δ[0] : SSet.{u}) ⟶ X} (H : SSet.Homotopy F G)
    (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightIntervalCylinderSection A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A Δ[0] ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightIntervalCylinderSection A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A Δ[0] ≫ G = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g)
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst A Δ[1] ≫ SSet.const x)
    (hy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm y) : SSet.Homotopy f g := by
  let K : Δ[1] ⊗ (A ⊗ Δ[1]) ⟶ X :=
    (α_ Δ[1] A Δ[1]).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightIntervalCylinderSection A ▷ Δ[1]) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A Δ[0] ▷ Δ[1]) ≫ H.h
  have h₀ : (Δ[1] ◁ (SSet.ι₀ : A ⟶ A ⊗ Δ[1])) ≫ K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app H.h₀ d)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A Δ[0]).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightIntervalCylinderSection A).app d z))).trans
        (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app hF d) z)
  have h₁ : (Δ[1] ◁ (SSet.ι₁ : A ⟶ A ⊗ Δ[1])) ≫ K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app H.h₁ d)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A Δ[0]).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightIntervalCylinderSection A).app d z))).trans
        (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app hG d) z)
  have hxl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A ⊗ Δ[1]) ≫ K = SSet.const x := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    have hc := congrArg
      (fun (q : (A ⊗ (Δ[0] : SSet.{u})) _⦋n⦌ ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A Δ[0]) _⦋n⦌) ↦
        q (a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := (Δ[0] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 0) n))
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero A (Δ[0] : SSet.{u})) (Opposite.op ⦋n⦌))
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A Δ[0]).app (Opposite.op ⦋n⦌)
      ((a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A Δ[0]).app (Opposite.op ⦋n⦌) a at hc
    change H.h.app (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A Δ[0]).app (Opposite.op ⦋n⦌)
        ((a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n),
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n), t) = _
    rw [hc]
    exact congrArg (fun (q : (A ⊗ Δ[1]) _⦋n⦌ ⟶ X _⦋n⦌) ↦ q (a, t))
      (NatTrans.congr_app hx (Opposite.op ⦋n⦌))
  have hyl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A ⊗ Δ[1]) ≫ K = SSet.const y := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    have hc := congrArg
      (fun (q : (A ⊗ (Δ[0] : SSet.{u})) _⦋n⦌ ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A Δ[0]) _⦋n⦌) ↦
        q (a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := (Δ[0] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 0) n))
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one A (Δ[0] : SSet.{u})) (Opposite.op ⦋n⦌))
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A Δ[0]).app (Opposite.op ⦋n⦌)
      ((a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A Δ[0]).app (Opposite.op ⦋n⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n) at hc
    change H.h.app (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A Δ[0]).app (Opposite.op ⦋n⦌)
        ((a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n),
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n), t) = _
    rw [hc]
    have hh := congrArg
      (fun (q : ((Δ[0] : SSet.{u}) ⊗ Δ[1]) _⦋n⦌ ⟶ X _⦋n⦌) ↦
        q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n, t))
      (NatTrans.congr_app hy (Opposite.op ⦋n⦌))
    exact hh.trans (congrArg (fun (q : (A ⊗ Δ[1]) _⦋n⦌ ⟶ X _⦋n⦌) ↦ q (a, t))
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.const_point_comp_yoneda (A := A ⊗ Δ[1]) y) (Opposite.op ⦋n⦌)))
  exact intervalMappingHomotopyOfSquare f g K hxl hyl h₀ h₁

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
