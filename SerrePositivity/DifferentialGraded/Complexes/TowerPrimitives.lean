module
public import SerrePositivity.DifferentialGraded.Complexes.ProductAcyclic

/-! # 全射的なacyclic複体の可算塔における互換な境界の原像

任意の逆極限の完全性は使わず、原像を補正しながら逐次選ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A]

lemma complexAcyclic_boundary {K : Complex A} (hK : K.Acyclic) (q : ℤ)
    (z : K.X q) (hz : K.d q (q + 1) z = 0) :
    ∃ t : K.X (q - 1), K.d (q - 1) q t = z := by
  have h := (HomologicalComplex.exactAt_iff' (K := K)
    (i := q - 1) (j := q) (k := q + 1) (by simp) (by simp)).1 (hK q)
  rw [ShortComplex.moduleCat_exact_iff] at h
  exact h z hz

lemma complexTower_primitive_step {K L : Complex A} (r : L ⟶ K)
    (hK : K.Acyclic) (hL : L.Acyclic)
    (hr : ∀ n : ℤ, Function.Surjective (r.f n)) (q : ℤ)
    (z : L.X q) (hz : L.d q (q + 1) z = 0)
    (t : K.X (q - 1)) (ht : K.d (q - 1) q t = r.f q z) :
    ∃ s : L.X (q - 1), L.d (q - 1) q s = z ∧ r.f (q - 1) s = t := by
  obtain ⟨b, hb⟩ := complexAcyclic_boundary (K := L) hL q z hz
  have hrb := congrArg (fun a => a b) (r.comm (q - 1) q)
  change K.d (q - 1) q (r.f (q - 1) b) = r.f q (L.d (q - 1) q b) at hrb
  rw [hb] at hrb
  have hw : K.d (q - 1) q (t - r.f (q - 1) b) = 0 := by
    rw [map_sub, ht, hrb, sub_self]
  obtain ⟨a, ha⟩ := complexAcyclic_boundary (K := K) hK (q - 1) (t - r.f (q - 1) b)
    (by rw [show q - 1 + 1 = q by omega]
        exact hw)
  obtain ⟨c, hc⟩ := hr (q - 1 - 1) a
  refine ⟨b + L.d (q - 1 - 1) (q - 1) c, ?_, ?_⟩
  · have hd := congrArg (fun a => a c) (L.d_comp_d (q - 1 - 1) (q - 1) q)
    change L.d (q - 1) q (L.d (q - 1 - 1) (q - 1) c) = 0 at hd
    rw [map_add, hb, hd, add_zero]
  · have hd := congrArg (fun a => a c) (r.comm (q - 1 - 1) (q - 1))
    change K.d (q - 1 - 1) (q - 1) (r.f (q - 1 - 1) c) =
      r.f (q - 1) (L.d (q - 1 - 1) (q - 1) c) at hd
    rw [hc, ha] at hd
    rw [map_add, ← hd]
    abel

lemma complexTower_compatible_primitives (K : ℕ → Complex A)
    (r : ∀ n, K (n + 1) ⟶ K n) (hK : ∀ n, (K n).Acyclic)
    (hr : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((r n).f q)) (q : ℤ)
    (z : ∀ n, (K n).X q) (hz : ∀ n, (K n).d q (q + 1) (z n) = 0)
    (hcompat : ∀ n, (r n).f q (z (n + 1)) = z n) :
    ∃ t : ∀ n, (K n).X (q - 1),
      (∀ n, (K n).d (q - 1) q (t n) = z n) ∧
      (∀ n, (r n).f (q - 1) (t (n + 1)) = t n) := by
  let P := fun n => { t : (K n).X (q - 1) // (K n).d (q - 1) q t = z n }
  have h0 := complexAcyclic_boundary (hK 0) q (z 0) (hz 0)
  have hstep (n : ℕ) (t : P n) : ∃ s : (K (n + 1)).X (q - 1),
      (K (n + 1)).d (q - 1) q s = z (n + 1) ∧ (r n).f (q - 1) s = t.val := by
    apply complexTower_primitive_step (r n) (hK n) (hK (n + 1)) (hr n) q
      (z (n + 1)) (hz (n + 1)) t.val
    exact t.property.trans (hcompat n).symm
  let t : (n : ℕ) → P n := Nat.rec
    ⟨Classical.choose h0, Classical.choose_spec h0⟩
    (fun n t => ⟨Classical.choose (hstep n t), (Classical.choose_spec (hstep n t)).1⟩)
  exact ⟨fun n => (t n).val, fun n => (t n).property,
    fun n => (Classical.choose_spec (hstep n (t n))).2⟩

end SerrePositivity.DifferentialGraded
