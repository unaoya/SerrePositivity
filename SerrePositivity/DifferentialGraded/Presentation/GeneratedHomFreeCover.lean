module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSpan
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomWordCardinality
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.SetTheory.Cardinal.Ordinal
/-!
概要：係数語の線形 span を固定した κ 個の自由基底で全射に被覆する。
方針：語の埋め込みを零で延長し、有限線形結合と span 帰納で全射性を示す。
規約：環の元の個数の上界は不要。語の生成子数と対象数だけを入力に保持する。
使われ方：c′ の実係数閉包を既存の固定基底 Hom 提示へ符号化する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord
variable {x y : J} {n : ℤ} {B : Type u}
  (e : DGGeneratedHomWord source target degree x y n ↪ B)

def freeCoverValues : B → linearSpan source target degree R D value coefficient x y n :=
  Function.extend e
    (fun a => ⟨evaluate source target degree R D value coefficient a,
      evaluate_mem_span source target degree R D value coefficient a⟩) (fun _ => 0)

def freeCover : (B →₀ R) →ₗ[R] linearSpan source target degree R D value coefficient x y n :=
  Finsupp.linearCombination R (freeCoverValues source target degree R D value coefficient e)

lemma freeCover_surjective :
    Function.Surjective (freeCover source target degree R D value coefficient e) := by
  intro a
  let L := freeCover source target degree R D value coefficient e
  have h : ∀ z (hz : z ∈ linearSpan source target degree R D value coefficient x y n),
      (⟨z, hz⟩ : linearSpan source target degree R D value coefficient x y n) ∈
        LinearMap.range L := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      refine ⟨Finsupp.single (e w) 1, ?_⟩
      change Finsupp.linearCombination R _ (Finsupp.single (e w) 1) = _
      rw [Finsupp.linearCombination_single]
      simp only [freeCoverValues, Function.Injective.extend_apply e.injective, one_smul]
    | zero => exact (LinearMap.range L).zero_mem
    | add f g _ _ hf hg => exact (LinearMap.range L).add_mem hf hg
    | smul a f _ hf => exact (LinearMap.range L).smul_mem a hf
  exact h a.val a.property

lemma fixedFreeCover_exists (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hI : Cardinal.mk I ≤ κ) (hJ : Cardinal.mk J ≤ κ) (x y : J) (n : ℤ) :
    ∃ q : (κ.ord.ToType →₀ R) →ₗ[R]
        linearSpan source target degree R D value coefficient x y n, Function.Surjective q := by
  have hcard : Cardinal.mk (DGGeneratedHomWord source target degree x y n) ≤
      Cardinal.mk κ.ord.ToType := by
    rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact cardinalMk_le source target degree κ hκ hI hJ x y n
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hcard
  exact ⟨freeCover source target degree R D value coefficient e,
    freeCover_surjective source target degree R D value coefficient e⟩

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
