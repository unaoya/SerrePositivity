module

public import SerrePositivity.InfinityCategories.F1B.PinchedIntervalEquivalence
public import SerrePositivity.InfinityCategories.F1B.KanSectionMappingSpaceIntervalComparison

/-!
概要：prism 上で両端を固定する図式ホモトピーから区間写像空間のホモトピーを作る。
方針：prism のパラメータを時間の前に置き、二重区間の図式を curry する。
規約：prism の値域 D は任意の単体集合。
使われ方：Kerodon §4.6.6、左右の fat join 図式のホモトピーの共通の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.KanSection
open PinchedInterval

/-- 概要：区間模型の族の零端点は始点に定値。
方針：境界の固定式を零端点で制限する。
規約：任意のパラメータ A。
使われ方：Kerodon §4.6.6、fat join の零端での貼り合わせ。 -/
lemma intervalMappingUncurry_zero {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    prismEndpoint 0 A ≫ intervalMappingUncurry f = SSet.const x := by
  calc
    _ = intervalBoundaryEndpoint 0 A ≫
        ((boundary 1).ι ▷ A) ≫ intervalMappingUncurry f := by
      rw [← Category.assoc, intervalBoundaryEndpoint_ι]
    _ = _ := by
      rw [intervalMappingUncurry_boundary, ← intervalMappingBoundary_diagram,
        intervalBoundaryDiagram_zero]

/-- 概要：区間模型の族の一端点は終点に定値。
方針：境界の固定式を一端点で制限する。
規約：任意のパラメータ A。
使われ方：Kerodon §4.6.6、fat join の一端での貼り合わせ。 -/
lemma intervalMappingUncurry_one {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    prismEndpoint 1 A ≫ intervalMappingUncurry f = SSet.const y := by
  calc
    _ = intervalBoundaryEndpoint 1 A ≫
        ((boundary 1).ι ▷ A) ≫ intervalMappingUncurry f := by
      rw [← Category.assoc, intervalBoundaryEndpoint_ι]
    _ = _ := by
      rw [intervalMappingUncurry_boundary, ← intervalMappingBoundary_diagram,
        intervalBoundaryDiagram_one]

/-- 概要：prism 上で始点と終点を固定した図式ホモトピーは区間模型の族のホモトピー。
方針：図式ホモトピーを prism で引き戻し、両端固定の二重区間の普遍性を使う。
規約：二つの時間端での図式の式と、写像の両端固定を別々に指定する。
使われ方：Kerodon §4.6.6、fat join 比較の同型から区間模型のホモトピーへの移行。 -/
noncomputable def intervalMappingHomotopyOfPrism {A D X : SSet.{u}} {x y : X _⦋0⦌}
    {F G : D ⟶ X} (H : SSet.Homotopy F G) (P : Δ[1] ⊗ A ⟶ D)
    (f g : A ⟶ intervalMappingSpace x y)
    (hF : P ≫ F = intervalMappingUncurry f) (hG : P ≫ G = intervalMappingUncurry g)
    (hx : ((prismEndpoint 0 A ≫ P) ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const x)
    (hy : ((prismEndpoint 1 A ≫ P) ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const y) :
    SSet.Homotopy f g := by
  let K : Δ[1] ⊗ (A ⊗ Δ[1]) ⟶ X := (α_ Δ[1] A Δ[1]).inv ≫ (P ▷ Δ[1]) ≫ H.h
  have h₀ : (Δ[1] ◁ (SSet.ι₀ : A ⟶ A ⊗ Δ[1])) ≫ K = intervalMappingUncurry f := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app H.h₀ d)
      (P.app d z)).trans (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app hF d) z)
  have h₁ : (Δ[1] ◁ (SSet.ι₁ : A ⟶ A ⊗ Δ[1])) ≫ K = intervalMappingUncurry g := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app H.h₁ d)
      (P.app d z)).trans (ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app hG d) z)
  have hxl : prismEndpoint 0 (A ⊗ Δ[1]) ≫ K = SSet.const x := by
    exact hx
  have hyl : prismEndpoint 1 (A ⊗ Δ[1]) ≫ K = SSet.const y := by
    exact hy
  exact intervalMappingHomotopyOfSquare f g K hxl hyl h₀ h₁

end SerrePositivity.InfinityCategories.KanSection
