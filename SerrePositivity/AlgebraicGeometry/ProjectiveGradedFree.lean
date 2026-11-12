module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedPresentation
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
概要：有限個の次数付き加群の積に、各成分の次数分解を移す。
方針：一つの成分にだけ値を置く写像を直和上に延ばし、有限個の成分で足す。
規約：加群ごとに整数の次数をずらしてから、この積の分解を使う。
使われ方：有限個の多項式環の捻りからの斉次自由表示を作る。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum BigOperators

variable {R ι κ : Type*} [CommRing R] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {M : κ → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]

/-- 有限積の次数成分を成分ごとに指定する。 -/
def projectiveGradedPiPiece (G : ι → (k : κ) → Submodule R (M k)) (i : ι) :
    Submodule R ((k : κ) → M k) :=
  Submodule.pi Set.univ (G i)

/-- 一つの成分だけに斉次元を置く加法写像。 -/
def projectiveGradedPiSingle (G : ι → (k : κ) → Submodule R (M k)) (i : ι) (k : κ) :
    G i k →+ projectiveGradedPiPiece G i where
  toFun x := ⟨Pi.single k x.val, by
    change ∀ l ∈ Set.univ, Pi.single k x.val l ∈ G i l
    intro l _
    by_cases h : l = k
    · subst l
      simpa using x.property
    · simp [Pi.single_apply, h]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp [Pi.single_add])

/-- 各成分の斉次元を戻して足すと、元の有限積の元になる。 -/
theorem projectiveGradedPiSingle_sum (G : ι → (k : κ) → Submodule R (M k))
    (i : ι) (x : projectiveGradedPiPiece G i) :
    ∑ k, projectiveGradedPiSingle G i k ⟨x.val k, x.property k (Set.mem_univ k)⟩ = x := by
  apply Subtype.ext
  funext k
  simp [projectiveGradedPiSingle, Finset.sum_apply, Pi.single_apply]

/-- 有限積は各成分の次数分解を受け継ぐ。 -/
@[instance_reducible]
def projectiveGradedPiDecomposition (G : ι → (k : κ) → Submodule R (M k))
    [∀ k, DirectSum.Decomposition (fun i ↦ G i k)] :
    DirectSum.Decomposition (projectiveGradedPiPiece G) := by
  classical
  let P := projectiveGradedPiPiece G
  let d (x : (k : κ) → M k) : ⨁ i, P i :=
    ∑ k, DirectSum.map (fun i ↦ projectiveGradedPiSingle G i k)
      (DirectSum.decompose (fun i ↦ G i k) (x k))
  have hsingle (k : κ) (z : ⨁ i, G i k) :
      DirectSum.coeAddMonoidHom P (DirectSum.map (fun i ↦ projectiveGradedPiSingle G i k) z) =
        Pi.single k (DirectSum.coeAddMonoidHom (fun i ↦ G i k) z) := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      dsimp only [P]
      simp only [DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
      rfl
    | add x y hx hy => simp [hx, hy, Pi.single_add]
  have hdadd (x y : (k : κ) → M k) : d (x + y) = d x + d y := by
    simp [d, DirectSum.decompose_add, map_add, Finset.sum_add_distrib]
  refine { decompose' := d, left_inv := ?_, right_inv := ?_ }
  · intro x
    change DirectSum.coeAddMonoidHom P (d x) = x
    simp only [d, map_sum, hsingle]
    have hx (k : κ) : DirectSum.coeAddMonoidHom (fun i ↦ G i k)
        (DirectSum.decompose (fun i ↦ G i k) (x k)) = x k :=
      (DirectSum.decompose (fun i ↦ G i k)).left_inv (x k)
    simp only [hx]
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  · intro z
    induction z using DirectSum.induction_on with
    | zero => simp [d]
    | of i x =>
      have hx (k : κ) : x.val k ∈ G i k := x.property k (Set.mem_univ k)
      rw [DirectSum.coeAddMonoidHom_of]
      change d x.val = DirectSum.of (fun i ↦ P i) i x
      simp only [d, DirectSum.decompose_of_mem (fun i ↦ G i _) (hx _), DirectSum.map_of]
      rw [← map_sum, projectiveGradedPiSingle_sum]
    | add x y hx hy =>
      rw [map_add, hdadd, hx, hy]

/-- 次数の添字を全単射で取り替えても、次数分解が得られる。 -/
@[instance_reducible]
def projectiveGradedReindexDecomposition {A J : Type*} [AddCommGroup A] [Module R A]
    [DecidableEq J] (G : ι → Submodule R A) [DirectSum.Decomposition G] (e : ι ≃ J) :
    DirectSum.Decomposition (fun j ↦ G (e.symm j)) := by
  classical
  let H := fun j ↦ G (e.symm j)
  let r := DirectSum.equivCongrLeft (β := fun i ↦ G i) e
  have hcoe (z : ⨁ j, H j) :
      DirectSum.coeAddMonoidHom G (r.symm z) = DirectSum.coeAddMonoidHom H z := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of j x =>
      have hr : r.symm (DirectSum.of (fun j ↦ H j) j x) = DirectSum.of (fun i ↦ G i) (e.symm j) x := by
        apply r.injective
        rw [r.apply_symm_apply]
        exact (DirectSum.equivCongrLeft_of (β := fun i ↦ G i) e j x).symm
      rw [hr, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine
    { decompose' := fun x ↦ r (DirectSum.decompose G x)
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    have h := hcoe (r (DirectSum.decompose G x))
    rw [r.symm_apply_apply] at h
    exact h.symm.trans ((DirectSum.decompose G).left_inv x)
  · intro z
    apply r.symm.injective
    rw [r.symm_apply_apply, ← hcoe]
    exact (DirectSum.decompose G).right_inv (r.symm z)

/-- 整数次数を定数だけずらした分解。 -/
@[instance_reducible]
def projectiveGradedShiftDecomposition {A : Type*} [AddCommGroup A] [Module R A]
    (G : ℤ → Submodule R A) [DirectSum.Decomposition G] (e : ℤ) :
    DirectSum.Decomposition (fun d ↦ G (d - e)) :=
  projectiveGradedReindexDecomposition G (Equiv.addRight e)

section FreePresentation

variable {S V : Type*} [CommRing S] [Algebra R S] [AddCommGroup V]
variable [Module R V] [Module S V] [IsScalarTower R S V]
variable (A : ℤ → Submodule R S) [SetLike.GradedMonoid A]
variable (G : ℤ → Submodule R V) [SetLike.GradedSMul A G]

/-- 指定した次数の生成元に対応する、有限自由加群の次数成分。 -/
def projectiveGradedFreePiece (degree : κ → ℤ) (d : ℤ) : Submodule R (κ → S) :=
  projectiveGradedPiPiece (fun d k ↦ A (d - degree k)) d

/-- 有限個の捻りの積の、次数分解。 -/
@[instance_reducible]
def projectiveGradedFreeDecomposition [DirectSum.Decomposition A] (degree : κ → ℤ) :
    DirectSum.Decomposition (projectiveGradedFreePiece A degree) := by
  letI (k : κ) : DirectSum.Decomposition (fun d ↦ A (d - degree k)) :=
    projectiveGradedShiftDecomposition A (degree k)
  exact projectiveGradedPiDecomposition (fun d k ↦ A (d - degree k))

/-- 斉次生成元による自由表示の写像は、各次数を保つ。 -/
theorem projectiveGradedFreeMap_mem (degree : κ → ℤ) (v : κ → V)
    (hv : ∀ k, v k ∈ G (degree k)) (d : ℤ) (x : projectiveGradedFreePiece A degree d) :
    Fintype.linearCombination S v x.val ∈ G d := by
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro k _
  have hx : x.val k ∈ A (d - degree k) := x.property k (Set.mem_univ k)
  have h := SetLike.GradedSMul.smul_mem hx (hv k)
  simpa only [vadd_eq_add, sub_add_cancel] using h

/-- 有限個の斉次生成元による自由表示は、生成の仮定から全射になる。 -/
theorem projectiveGradedFreeMap_surjective (v : κ → V)
    (hv : Submodule.span S (Set.range v) = ⊤) :
    Function.Surjective (Fintype.linearCombination S v) :=
  (span_range_eq_top_iff_surjective_fintypeLinearCombination S v).mp hv

end FreePresentation

end SerrePositivity.AlgebraicGeometry
