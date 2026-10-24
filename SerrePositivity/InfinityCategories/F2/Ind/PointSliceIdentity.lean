module

public import SerrePositivity.InfinityCategories.F1B.Cones.SliceIdentityTerminal

/-!
概要：任意の元の点写像の slice の恒等頂点は終対象。
方針：元の点写像を保持して恒等錐を表示し、標準頂点の恒等錐の終対象性へ戻す。
規約：元の点写像と全切断を選び直さない。
使われ方：旧族の全円柱を固定する相対余錐延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：任意の元の点写像の slice の恒等頂点は終対象。
方針：元の点写像を保持して恒等錐を表示し、標準頂点の恒等錐の終対象性へ戻す。
規約：元の全射を保持。使われ方：終点を固定する相対再構成。 -/
def pointSliceIdentity {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) : (sliceOver p) _⦋0⦌ :=
  ⟨SSet.const (SSet.yonedaEquiv p), by
    rw [SSet.comp_const, ← SSet.yonedaEquiv_symm_zero, Equiv.symm_apply_apply]⟩
/-- 概要：任意の元の点写像の slice の恒等頂点は終対象。
方針：元の点写像を保持して恒等錐を表示し、標準頂点の恒等錐の終対象性へ戻す。
規約：元の全射を保持。使われ方：終点を固定する相対再構成。 -/
lemma pointSliceIdentity_isTerminal {X : SSet.{u}} [Quasicategory X]
    (p : (Δ[0] : SSet.{u}) ⟶ X) : IsTerminalVertex (pointSliceIdentity p) := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective p
  have h : pointSliceIdentity (SSet.yonedaEquiv.symm x) = sliceIdentityCone x := by
    apply Subtype.ext
    simp only [pointSliceIdentity, Equiv.apply_symm_apply, sliceIdentityCone]
  rw [h]
  exact F1B.sliceIdentityCone_isTerminalVertex x

end SerrePositivity.InfinityCategories.F2.Ind
