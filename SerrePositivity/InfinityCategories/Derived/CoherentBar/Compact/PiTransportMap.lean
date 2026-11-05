module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.FilteredSpaceBridgeInput
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
/-!
概要：道を境界に指定した π の基点移送は、元の空間の射で後合成できる。
方針：球面代表と円柱を同じ実射で後合成し、境界の道も同じ射で送る。
規約：基点の移動を忘れず、指定道の像を使う。
使われ方：実加法模型と native 評価空間の比較による移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial

lemma dgBarCompactPiTransport_map {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) (q : X ⟶ Y) {x y : X _⦋0⦌} (e : X.Edge x y)
    {a : KanHomotopyGroup X n x} {b : KanHomotopyGroup X n y}
    (h : dgBarCompactPiTransport n e a b) :
    dgBarCompactPiTransport n (e.map q)
      (dgBarCompactPiMap n q x a) (dgBarCompactPiMap n q y b) := by
  obtain ⟨f, g, hf, hg, H, hH⟩ := h
  refine ⟨mapSimplex q rfl f, mapSimplex q rfl g, ?_, ?_,
    functorHomotopyPostcomp H q, ?_⟩
  · change KanHomotopyGroup.map q rfl (KanHomotopyGroup.mk f) = _
    rw [hf]
    rfl
  · change KanHomotopyGroup.map q rfl (KanHomotopyGroup.mk g) = _
    rw [hg]
    rfl
  · change ((SSet.boundary (n + 1)).ι ▷ Δ[1]) ≫ (H.h ≫ q) = _
    rw [← Category.assoc, hH, Category.assoc]
    congr 1
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl

end SerrePositivity.InfinityCategories
