module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFatHomotopy

/-!
概要：prism 上で両端を固定する図式ホモトピーから区間写像空間のホモトピーを作る。
方針：prism のパラメータを時間の前に置き、二重区間の図式を curry する。
規約：prism の値域 D は任意の単体集合。
使われ方：Kerodon §4.6.6（Tag 04HY）、左右の fat join 図式のホモトピーの共通の移送。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：prism 上で始点と終点を固定した図式ホモトピーは区間模型の族のホモトピー。
方針：図式ホモトピーを prism で引き戻し、両端固定の二重区間の普遍性を使う。
規約：二つの時間端での図式の式と、写像の両端固定を別々に指定する。
使われ方：Kerodon §4.6.6（Tag 04HY）、fat join 比較の同型から区間模型のホモトピーへの移行。 -/
noncomputable def intervalMappingHomotopyOfPrism {A D X : SSet.{u}} {x y : X _⦋0⦌}
    {F G : D ⟶ X} (H : SSet.Homotopy F G) (P : Δ[1] ⊗ A ⟶ D)
    (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)
    (hF : P ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f) (hG : P ≫ G = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g)
    (hx : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ P) ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const x)
    (hy : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ P) ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const y) :
    SSet.Homotopy f g := by
  let K : Δ[1] ⊗ (A ⊗ Δ[1]) ⟶ X := (α_ Δ[1] A Δ[1]).inv ≫ (P ▷ Δ[1]) ≫ H.h
  have h₀ : (Δ[1] ◁ (SSet.ι₀ : A ⟶ A ⊗ Δ[1])) ≫ K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app H.h₀ d)
      (P.app d z)).trans (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app hF d) z)
  have h₁ : (Δ[1] ◁ (SSet.ι₁ : A ⟶ A ⊗ Δ[1])) ≫ K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app H.h₁ d)
      (P.app d z)).trans (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app hG d) z)
  have hxl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A ⊗ Δ[1]) ≫ K = SSet.const x := by
    exact hx
  have hyl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A ⊗ Δ[1]) ≫ K = SSet.const y := by
    exact hy
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingHomotopyOfSquare f g K hxl hyl h₀ h₁

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
