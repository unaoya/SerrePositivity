module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureRows
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-! # 全path直和上のε消去作用素

閉じた次数+1の各消去和をshift先へのchain mapへ移し、直和の普遍性で貼り合わせる。
得られる作用素は内部微分と反交換する。作用素自身の二乗零は別に証明する必要がある。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 各pathの閉じた消去和を次数+1のcocycleとして保持する。 -/
def eraseRowCycle {S : Set D} (w : Word S) (x y : D) :
    Cocycle (term A D w x y) (internalHom A D S x y) 1 :=
  Cocycle.mk (eraseRow A D w x y) 2 (by omega) (eraseRow_closed A D w x y)

/-- 直和普遍性によるshift先への消去chain map。 -/
def erasureToShift (S : Set D) (x y : D) :
    internalHom A D S x y ⟶ (internalHom A D S x y)⟦(1 : ℤ)⟧ :=
  Sigma.desc (fun w => Cocycle.equivHomShift.symm (eraseRowCycle A D w x y))

lemma ι_erasureToShift (S : Set D) (x y : D) (w : Word S) :
    ι A D S x y w ≫ erasureToShift A D S x y =
      Cocycle.equivHomShift.symm (eraseRowCycle A D w x y) :=
  Sigma.ι_comp_desc _ _

/-- 全path直和上の次数+1のε消去cocycle。 -/
def erasureCycle (S : Set D) (x y : D) :
    Cocycle (internalHom A D S x y) (internalHom A D S x y) 1 :=
  Cocycle.equivHomShift (erasureToShift A D S x y)

/-- 内部微分に加える、path長を一つ下げる次数+1の作用素。 -/
def erasure (S : Set D) (x y : D) :
    Cochain (internalHom A D S x y) (internalHom A D S x y) 1 :=
  (erasureCycle A D S x y).val

lemma erasure_closed (S : Set D) (x y : D) : δ 1 2 (erasure A D S x y) = 0 :=
  Cocycle.δ_eq_zero _ _

/-- 作用素を各pathへ制限すると、元の有限消去和になる。 -/
lemma erasure_precomp (S : Set D) (x y : D) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp (erasure A D S x y) (zero_add 1) =
      eraseRow A D w x y := by
  have h := congrArg (fun f => (Cocycle.equivHomShift f).val)
    (ι_erasureToShift A D S x y w)
  rw [Cocycle.equivHomShift_comp, AddEquiv.apply_symm_apply] at h
  exact h

/-- 元のHomに対応する空path上ではε消去は零。 -/
lemma erasure_originalHom (S : Set D) (x y : D) :
    (Cochain.ofHom (originalHom A D S x y)).comp (erasure A D S x y) (zero_add 1) = 0 := by
  exact (erasure_precomp A D S x y []).trans (eraseRow_nil A D S x y)

/-- 各path上で二重消去は、最初のfaceと短いpathの消去和の合成の有限和になる。 -/
lemma erasure_square_precomp (S : Set D) (x y : D) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp
      ((erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega))
      (zero_add 2) =
    ∑ i ∈ Finset.range w.length, (eraseFace A D w i x y).comp
      (eraseRow A D (w.eraseIdx i) x y) (show (1 : ℤ) + 1 = 2 by omega) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, erasure_precomp]
  let R : Cochain (term A D w x y) (internalHom A D S x y) 1 →+
      Cochain (term A D w x y) (internalHom A D S x y) 2 :=
    { toFun := fun f => f.comp (erasure A D S x y) (by omega)
      map_zero' := Cochain.zero_comp _ _
      map_add' := fun f g => Cochain.add_comp f g _ _ }
  change R (eraseRow A D w x y) = _
  rw [eraseRow, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (eraseSummand A D w i x y).comp (erasure A D S x y) (by omega) = _
  rw [eraseSummand, Cochain.comp_assoc_of_second_is_zero_cochain, erasure_precomp]

/-- 空pathでは二重消去も零。 -/
lemma erasure_square_originalHom (S : Set D) (x y : D) :
    (Cochain.ofHom (originalHom A D S x y)).comp
      ((erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega))
      (zero_add 2) = 0 := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, erasure_originalHom]
  exact Cochain.zero_comp _ _

/-- 長さ1のpathは一度消去すると空pathとなるため、二重消去は零。 -/
lemma erasure_square_singleton {S : Set D} (b : S) (x y : D) :
    (Cochain.ofHom (ι A D S x y [b])).comp
      ((erasure A D S x y).comp (erasure A D S x y) (show (1 : ℤ) + 1 = 2 by omega))
      (zero_add 2) = 0 := by
  rw [erasure_square_precomp]
  simp only [List.length_cons, List.length_nil, zero_add, Finset.range_one,
    Finset.sum_singleton]
  change (eraseFirst A D b [] x y).comp (eraseRow A D ([] : Word S) x y) (by omega) = 0
  rw [eraseRow_nil]
  exact Cochain.comp_zero _ _

end SerrePositivity.DifferentialGraded.DGQuotient
