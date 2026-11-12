module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeTerminalTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeTerminalFamilyHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle

/-!
概要：元の底を固定する三つの比較円柱を、同じ底の上の三角形の族へ充填する。
方針：三円柱を関手辺に移し、関手空間の相対終点境界充填を使う。
規約：三円柱全体を保持。使われ方：部分極限族の二脚と共通対角辺の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 底を全時刻で固定する円柱の curry は、元の図式の恒等辺の上にある。 -/
lemma curry_relativeHomotopy_post_eq_const {A E D : SSet.{u}} (p : E ⟶ D)
    {f g : A ⟶ E} (H : SSet.Homotopy f g) (a : A ⟶ D)
    (hH : H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ a) :
    curry H.h ≫ (ihom A).map p = SSet.const (functorVertex a) := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_curry, uncurry_const_functorVertex]
  exact hH

/-- 相対終対象の族への三つの指定円柱は、同じ底を固定する全三角形へ充填できる。 -/
lemma relativeTerminalFamilyTriangle {A E D : SSet.{u}} (p : E ⟶ D) (a : A ⟶ D)
    {f g h : A ⟶ E} (ht : ∀ x : A _⦋0⦌,
      TerminalBoundaryLifting p (h.app (Opposite.op ⦋0⦌) x))
    (l : SSet.Homotopy f g) (r : SSet.Homotopy g h) (d : SSet.Homotopy f h)
    (hl : l.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ a)
    (hr : r.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ a)
    (hd : d.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ a) :
    Nonempty {T : FunctorCompositionTriangle l r d //
      T.diagram ≫ (ihom A).map p = SSet.const (functorVertex a)} := by
  let e := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy l)
  let k := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy r)
  let t := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy d)
  have he : SSet.yonedaEquiv.symm e.edge ≫ (ihom A).map p =
      SSet.const (functorVertex a) := by
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry l.h)) ≫ _ = _
    rw [Equiv.symm_apply_apply]
    exact curry_relativeHomotopy_post_eq_const p l a hl
  have hk : SSet.yonedaEquiv.symm k.edge ≫ (ihom A).map p =
      SSet.const (functorVertex a) := by
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry r.h)) ≫ _ = _
    rw [Equiv.symm_apply_apply]
    exact curry_relativeHomotopy_post_eq_const p r a hr
  have hd' : SSet.yonedaEquiv.symm t.edge ≫ (ihom A).map p =
      SSet.const (functorVertex a) := by
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry d.h)) ≫ _ = _
    rw [Equiv.symm_apply_apply]
    exact curry_relativeHomotopy_post_eq_const p d a hd
  obtain ⟨T, h0, h1, h2, hT⟩ := relativeTerminal_triangle ((ihom A).map p)
    (functorVertex a) (terminalBoundaryLifting_ihom_of_pointwise p h ht) e k t he hk hd'
  refine ⟨⟨⟨T, ?_, ?_, ?_⟩, hT⟩⟩
  · change _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry r.h)) at h0
    rwa [Equiv.symm_apply_apply] at h0
  · change _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry d.h)) at h1
    rwa [Equiv.symm_apply_apply] at h1
  · change _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry l.h)) at h2
    rwa [Equiv.symm_apply_apply] at h2

end SerrePositivity.InfinityCategories.F2
