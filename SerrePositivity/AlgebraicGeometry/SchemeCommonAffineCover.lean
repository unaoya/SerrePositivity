module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCech
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
概要：二つのアフィン開被覆の共通細分を、開集合の交叉で作る。
方針：添字の直積を取り、アフィン対角の下で交叉のアフィン性を使う。
規約：有限被覆の場合には添字の直積も有限。分離的なスキームに適用できる。
使われ方：細分の Čech H の同型を、任意の二つの有限アフィン被覆の比較にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {ι κ : Type}
variable (U : ι → X.Opens) (V : κ → X.Opens)

/-- 二つの開被覆の交叉による共通細分。 -/
def schemeCommonOpenCover (ij : ι × κ) : X.Opens := U ij.1 ⊓ V ij.2

/-- 二つの被覆の交叉も全空間を被覆する。 -/
theorem schemeCommonOpenCover_iSup (hU : (⨆ i, U i) = ⊤) (hV : (⨆ j, V j) = ⊤) :
    (⨆ ij, schemeCommonOpenCover U V ij) = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  have hxU : x ∈ ⨆ i, U i := by rw [hU]; exact hx
  have hxV : x ∈ ⨆ j, V j := by rw [hV]; exact hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxV
  exact Opens.mem_iSup.mpr ⟨(i, j), ⟨hi, hj⟩⟩

/-- 共通細分から最初の被覆への包含。 -/
theorem schemeCommonOpenCover_le_left (ij : ι × κ) :
    schemeCommonOpenCover U V ij ≤ U ij.1 := inf_le_left

/-- 共通細分から二つ目の被覆への包含。 -/
theorem schemeCommonOpenCover_le_right (ij : ι × κ) :
    schemeCommonOpenCover U V ij ≤ V ij.2 := inf_le_right

/-- アフィン対角のスキームでは、共通細分もアフィン開被覆。 -/
theorem schemeCommonOpenCover_isAffineOpen
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j)) (ij : ι × κ) :
    IsAffineOpen (schemeCommonOpenCover U V ij) := (hU ij.1).inf (hV ij.2)

/-- アフィン対角のスキームのアフィン開の非空有限交叉はアフィン。 -/
theorem cechOpenIntersection_isAffineOpen [DecidableEq ι]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hU : ∀ i, IsAffineOpen (U i)) (T : Finset ι) (hT : T.Nonempty) :
    IsAffineOpen (cechOpenIntersection U T) :=
  IsAffineOpen.biInf (T : Set ι) T.finite_toSet hT (fun i _ ↦ hU i)

end SerrePositivity.AlgebraicGeometry
