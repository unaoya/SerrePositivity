module

public import SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCover
public import Mathlib.Data.Fintype.EquivFin

/-!
概要：有限共通被覆の添字を Fin n に取り直し、順序付き Čech API に渡す。
方針：添字の直積と Fin との同値を用い、開集合と二つの射影を同時に移す。
規約：直積に新しい順序を仮定しない。
使われ方：二つの有限アフィン被覆の比較同型。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {Y : Scheme.{u}} {ι κ : Type} [Fintype ι] [Fintype κ]
variable (U : ι → Y.Opens) (V : κ → Y.Opens)

/-- Fin で添字付けした、有限の共通開被覆。 -/
def schemeFiniteCommonOpenCover (k : Fin (Fintype.card (ι × κ))) : Y.Opens :=
  schemeCommonOpenCover U V ((Fintype.equivFin (ι × κ)).symm k)

/-- 有限の共通被覆から第一の被覆への添字。 -/
def schemeFiniteCommonCoverLeft (k : Fin (Fintype.card (ι × κ))) : ι :=
  ((Fintype.equivFin (ι × κ)).symm k).1

/-- 有限の共通被覆から第二の被覆への添字。 -/
def schemeFiniteCommonCoverRight (k : Fin (Fintype.card (ι × κ))) : κ :=
  ((Fintype.equivFin (ι × κ)).symm k).2

/-- 有限共通被覆の全空間の被覆性。 -/
theorem schemeFiniteCommonOpenCover_iSup (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤) :
    (⨆ k, schemeFiniteCommonOpenCover U V k) = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  have hu : x ∈ ⨆ i, U i := by rw [hU]; exact hx
  have hv : x ∈ ⨆ j, V j := by rw [hV]; exact hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hu
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hv
  apply Opens.mem_iSup.mpr
  refine ⟨Fintype.equivFin (ι × κ) (i, j), ?_⟩
  simpa only [schemeFiniteCommonOpenCover, schemeCommonOpenCover, Equiv.symm_apply_apply] using (show x ∈ U i ⊓ V j from ⟨hi, hj⟩)

/-- 有限共通被覆から第一の被覆への包含。 -/
theorem schemeFiniteCommonOpenCover_le_left (k : Fin (Fintype.card (ι × κ))) :
    schemeFiniteCommonOpenCover U V k ≤ U (schemeFiniteCommonCoverLeft (ι := ι) (κ := κ) k) :=
  inf_le_left

/-- 有限共通被覆から第二の被覆への包含。 -/
theorem schemeFiniteCommonOpenCover_le_right (k : Fin (Fintype.card (ι × κ))) :
    schemeFiniteCommonOpenCover U V k ≤ V (schemeFiniteCommonCoverRight (ι := ι) (κ := κ) k) :=
  inf_le_right

/-- アフィン対角の下で、有限共通被覆の各開集合はアフィン。 -/
theorem schemeFiniteCommonOpenCover_isAffineOpen
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (k : Fin (Fintype.card (ι × κ))) : IsAffineOpen (schemeFiniteCommonOpenCover U V k) :=
  schemeCommonOpenCover_isAffineOpen U V hU hV _

end SerrePositivity.AlgebraicGeometry
