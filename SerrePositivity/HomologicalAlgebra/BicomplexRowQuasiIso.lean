module

public import SerrePositivity.HomologicalAlgebra.BicomplexComponents
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection
import all SerrePositivity.HomologicalAlgebra.BicomplexComponents

/-!
# 行が完全な第一象限総複体

## 概要
正の縦次数の行が完全なら、第 0 行への射影は擬同型になる。

## 方針
射影の核にある余輪体を、縦次数の小さい成分から順に余境界で消す。

## 規約
固定した総次数には有限個の成分だけがある。

## 使われ方
pd de Rham 総複体から pd Čech 複体への比較。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SerrePositivity.HomologicalAlgebra

variable {R : Type u} [CommRing R]
local notation "up" => ComplexShape.up ℕ

variable (K : HomologicalComplex₂ (ModuleCat.{u} R) up up) [K.HasTotal up]

private def VanishesBelow (n b : ℕ) (x : (K.total up).X n) : Prop :=
  ∀ a j (h : a + j = n), j < b → componentAt K n ⟨(a, j), h⟩ x = 0

set_option maxHeartbeats 800000 in
-- 総微分の成分表示と成分の台を照合する。
private theorem horizontalClosed (a b n : ℕ) (h : a + b = n) (x : (K.total up).X n)
    (hx : (K.total up).d n (n + 1) x = 0) (hl : VanishesBelow K n b x) :
    (K.d a (a + 1)).f b (componentAt K n ⟨(a, b), h⟩ x) = 0 := by
  cases b with
  | zero =>
    have hn : n = a := by omega
    subst n
    have he := ConcreteCategory.congr_hom (totalD_component_zeroRight K a) x
    change componentAt K (a + 1) ⟨(a + 1, 0), Nat.add_zero _⟩ ((K.total up).d a (a + 1) x) =
      (K.d a (a + 1)).f 0 (componentAt K a ⟨(a, 0), Nat.add_zero _⟩ x) at he
    have hx' : (K.total up).d a (a + 1) x = 0 := hx
    rw [hx', map_zero] at he
    exact he.symm
  | succ b =>
    have h' : a + b + 1 = n := by omega
    have he := ConcreteCategory.congr_hom (totalD_component_succ K a b n h') x
    change componentAt K (n + 1) ⟨(a + 1, b + 1), by omega⟩ ((K.total up).d n (n + 1) x) =
      (K.d a (a + 1)).f (b + 1) (componentAt K n ⟨(a, b + 1), by omega⟩ x) +
        (-1 : ℤ)^(a + 1) •
          (K.X (a + 1)).d b (b + 1) (componentAt K n ⟨(a + 1, b), by omega⟩ x) at he
    rw [hx, map_zero, hl (a + 1) b (by omega) (Nat.lt_succ_self b), map_zero,
      smul_zero, add_zero] at he
    exact he.symm

omit [K.HasTotal up] in
private theorem rowBoundary {a b : ℕ} (h : (bicomplexRow K b).ExactAt a)
    (x : (K.X a).X b) (hx : (K.d a (a + 1)).f b x = 0) :
    ∃ y : (K.X (a - 1)).X b, (K.d (a - 1) a).f b y = x := by
  have hp : (ComplexShape.up ℕ).prev a = a - 1 := by cases a with
    | zero => exact CochainComplex.prev_nat_zero
    | succ a => exact CochainComplex.prev_nat_succ a
  have he := ((bicomplexRow K b).exactAt_iff' (a - 1) a (a + 1) hp (CochainComplex.next ℕ a)).mp h
  exact (ShortComplex.moduleCat_exact_iff _).mp he x hx

private theorem removeRow (n b c : ℕ) (hc : c ≤ b)
    (hK : ∀ a, (bicomplexRow K b).ExactAt a) (z : (K.total up).X (n + 1))
    (hz : (K.total up).d (n + 1) (n + 2) z = 0) (hl : VanishesBelow K (n + 1) b z) :
    ∃ y : (K.total up).X n, VanishesBelow K n c y ∧
      VanishesBelow K (n + 1) (b + 1) (z - (K.total up).d n (n + 1) y) := by
  by_cases hbn : b ≤ n + 1
  · let a := n + 1 - b
    have hab : a + b = n + 1 := by omega
    let x := componentAt K (n + 1) ⟨(a, b), hab⟩ z
    have hc : (K.d a (a + 1)).f b x = 0 := horizontalClosed K a b (n + 1) hab z hz hl
    cases ha : a with
    | zero =>
      have hx : x = 0 := by
        have h0 : (K.d a (a + 1)).f b x = 0 := hc
        obtain ⟨w, hw⟩ := rowBoundary K (hK a) x h0
        have hshape : (K.d (a - 1) a).f b = 0 := by
          rw [K.shape _ _ (by change ¬ (a - 1) + 1 = a; omega)]
          rfl
        rw [hshape] at hw
        exact hw.symm
      refine ⟨0, ?_, ?_⟩
      · intro i j hij hj
        exact map_zero _
      · intro i j hij hj
        rw [map_zero, sub_zero]
        by_cases e : j = b
        · subst j
          have hi : i = a := by omega
          subst i
          exact hx
        · exact hl i j hij (by omega)
    | succ c' =>
      have hcn : c'+b = n := by omega
      have hcb : (c'+1) + b = n + 1 := by omega
      let x' := componentAt K (n + 1) ⟨(c'+1, b), hcb⟩ z
      have hx' := horizontalClosed K (c'+1) b (n + 1) hcb z hz hl
      obtain ⟨w, hw⟩ := rowBoundary K (hK (c'+1)) x' hx'
      let w' : (K.X c').X b := w
      have hw' : (K.d c' (c'+1)).f b w' = x' := hw
      let y := insertAt K n ⟨(c', b), hcn⟩ w'
      refine ⟨y, ?_, ?_⟩
      · intro i j hij hj
        have hne : (⟨(c', b), hcn⟩ : totalIndex n) ≠ ⟨(i, j), hij⟩ := by
          intro h
          have h' := congrArg (fun t : totalIndex n => t.1.2) h
          dsimp at h'
          omega
        exact ConcreteCategory.congr_hom (insertAt_componentAt_ne K _ _ hne) w'
      · intro i j hij hj
        rw [map_sub]
        by_cases e : j = b
        · subst j
          have hi : i = c'+1 := by omega
          subst i
          have hc' := ConcreteCategory.congr_hom
            (insertAt_total_d_component_horizontal K hcn) w'
          change componentAt K (n + 1) _ ((K.total up).d n (n + 1) y) = _ at hc'
          rw [hc', hw']
          exact sub_self _
        · have hj' : j < b := by omega
          rw [hl i j hij hj']
          have hc' := ConcreteCategory.congr_hom (insertAt_total_d_component_lower K hcn hij hj') w'
          change componentAt K (n + 1) _ ((K.total up).d n (n + 1) y) = 0 at hc'
          rw [hc', sub_zero]
  · refine ⟨0, ?_, ?_⟩
    · intro a j h hj
      exact map_zero _
    · intro a j h hj
      rw [map_zero, sub_zero]
      exact hl a j h (by omega)

private theorem rowZero_f (n : ℕ) :
    (totalToRowZero K).f n = componentAt K n ⟨(n, 0), Nat.add_zero _⟩ := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = n at h
  by_cases hb : b = 0
  · subst b
    simp only [Nat.add_zero] at h
    subst n
    simpa [totalToRowZero, rowZeroApp, componentAt] using
      (ιTotal_totalComponent K a 0).symm
  · have hne : a ≠ n := by omega
    simp [totalToRowZero, rowZeroApp, componentAt, hb, totalComponent, hne]

private theorem rowZero_f_surjective (n : ℕ) : Function.Surjective ((totalToRowZero K).f n) := by
  intro x
  refine ⟨insertAt K n ⟨(n, 0), Nat.add_zero _⟩ x, ?_⟩
  rw [rowZero_f]
  exact ConcreteCategory.congr_hom
    (insertAt_componentAt_eq K (⟨(n, 0), Nat.add_zero _⟩ : totalIndex n)) x

private theorem belowOne_of_projection_zero (n : ℕ) (x : (K.total up).X n)
    (h : (totalToRowZero K).f n x = 0) : VanishesBelow K n 1 x := by
  intro a j ha hj
  have hj' : j = 0 := by omega
  subst j
  have ha' : a = n := by omega
  subst a
  simpa only [rowZero_f] using h

private theorem projection_zero_of_belowOne (n : ℕ) (x : (K.total up).X n)
    (h : VanishesBelow K n 1 x) : (totalToRowZero K).f n x = 0 := by
  rw [rowZero_f]
  exact h n 0 (Nat.add_zero _) (by decide)

private theorem below_add {n b : ℕ} {x y : (K.total up).X n}
    (hx : VanishesBelow K n b x) (hy : VanishesBelow K n b y) :
    VanishesBelow K n b (x + y) := by
  intro a j h hj
  rw [map_add, hx a j h hj, hy a j h hj, add_zero]

private theorem removeAllRows (c : ℕ)
    (hK : ∀ a b, c ≤ b → (bicomplexRow K b).ExactAt a)
    (n : ℕ) (z : (K.total up).X (n + 1))
    (hz : (K.total up).d (n + 1) (n + 2) z = 0) (hl : VanishesBelow K (n + 1) c z) :
    ∃ y : (K.total up).X n, VanishesBelow K n c y ∧ (K.total up).d n (n + 1) y = z := by
  have h (b : ℕ) : ∃ y : (K.total up).X n, VanishesBelow K n c y ∧
      VanishesBelow K (n + 1) (c + b) (z - (K.total up).d n (n + 1) y) := by
    induction b with
    | zero =>
      refine ⟨0, fun _ _ _ _ => map_zero _, ?_⟩
      rw [map_zero, sub_zero]
      exact hl
    | succ b ih =>
      obtain ⟨y, hy, hy'⟩ := ih
      let w := z - (K.total up).d n (n + 1) y
      have hw : (K.total up).d (n + 1) (n + 2) w = 0 := by
        change (K.total up).d (n + 1) (n + 2) (z - (K.total up).d n (n + 1) y) = 0
        rw [map_sub, hz, ← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
        change 0 - (0 : (K.total up).X (n + 2)) = 0
        exact sub_zero _
      have hc : c ≤ c + b := Nat.le_add_right c b
      obtain ⟨t, ht, ht'⟩ := removeRow K n (c + b) c hc (fun a => hK a (c + b) hc) w hw hy'
      refine ⟨y + t, below_add K hy ht, ?_⟩
      rw [map_add, ← sub_sub]
      exact ht'
  obtain ⟨y, hy, hy'⟩ := h (n + 2)
  refine ⟨y, hy, (sub_eq_zero.mp (totalComponent_ext_zero K _ ?_)).symm⟩
  intro a j hj
  exact hy' a j hj (by omega)

private abbrev rowZeroKernelTerm (n : ℕ) := LinearMap.ker ((totalToRowZero K).f n).hom

private def rowZeroKernelD (n : ℕ) : rowZeroKernelTerm K n →ₗ[R] rowZeroKernelTerm K (n + 1) :=
  (((K.total up).d n (n + 1)).hom.comp (rowZeroKernelTerm K n).subtype).codRestrict _
    (fun x => by
      have hh := ConcreteCategory.congr_hom ((totalToRowZero K).comm n (n + 1)) x.1
      change (totalToRowZero K).f (n + 1) ((K.total up).d n (n + 1) x.1) = 0
      have hx : (totalToRowZero K).f n x.1 = 0 := x.2
      exact hh.symm.trans (by rw [ConcreteCategory.comp_apply, hx, map_zero]))

private def rowZeroKernel : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (rowZeroKernelTerm K n))
    (fun n => ModuleCat.ofHom (rowZeroKernelD K n))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact ConcreteCategory.congr_hom ((K.total up).d_comp_d n (n + 1) (n + 2)) x.1)

private def rowZeroKernelInclusion : rowZeroKernel K ⟶ K.total up where
  f n := ModuleCat.ofHom (rowZeroKernelTerm K n).subtype
  comm' n m h := by
    have h' : n + 1 = m := h
    subst m
    dsimp only [rowZeroKernel, CochainComplex.of]
    rw [CochainComplex.of_d]
    rfl

private def rowZeroShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (rowZeroKernelInclusion K) (totalToRowZero K) (by
    ext n x
    exact x.2)

private theorem rowZeroShortExact : (rowZeroShortComplex K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  · exact (ModuleCat.epi_iff_surjective _).mpr (rowZero_f_surjective K n)

private theorem rowZeroKernel_exact (hK : ∀ a b, 0 < b → (bicomplexRow K b).ExactAt a)
    (n : ℕ) : (rowZeroKernel K).ExactAt n := by
  have hp : (ComplexShape.up ℕ).prev n = n - 1 := by cases n with
    | zero => exact CochainComplex.prev_nat_zero
    | succ n => exact CochainComplex.prev_nat_succ n
  apply ((rowZeroKernel K).exactAt_iff' (n - 1) n (n + 1) hp (CochainComplex.next ℕ n)).mpr
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  let x : (K.total up).X n := z.1
  have hx := belowOne_of_projection_zero K n x z.2
  have hd : (K.total up).d n (n + 1) x = 0 := by
    have he : (rowZeroKernel K).d n (n + 1) z = 0 := hz
    dsimp only [rowZeroKernel, CochainComplex.of] at he
    rw [CochainComplex.of_d] at he
    exact congrArg Subtype.val he
  cases n with
  | zero =>
    have hzero : x = 0 := totalComponent_ext_zero K x fun a j h =>
      hx a j h (by omega)
    exact ⟨0, by rw [map_zero]; exact Subtype.ext hzero.symm⟩
  | succ n =>
    obtain ⟨y, hy, hy'⟩ := removeAllRows K 1 hK n x hd hx
    refine ⟨⟨y, projection_zero_of_belowOne K n y hy⟩, ?_⟩
    change (rowZeroKernel K).d n (n + 1) _ = z
    dsimp only [rowZeroKernel, CochainComplex.of]
    rw [CochainComplex.of_d]
    exact Subtype.ext hy'

/-- 全ての行が完全なら、第一象限の総複体も完全。 -/
theorem bicomplexTotal_exactAt_of_rows
    (hK : ∀ a b, (bicomplexRow K b).ExactAt a) (n : ℕ) : (K.total up).ExactAt n := by
  have hp : (ComplexShape.up ℕ).prev n = n - 1 := by cases n with
    | zero => exact CochainComplex.prev_nat_zero
    | succ n => exact CochainComplex.prev_nat_succ n
  apply ((K.total up).exactAt_iff' (n - 1) n (n + 1) hp (CochainComplex.next ℕ n)).mpr
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  cases n with
  | zero =>
    have hc := horizontalClosed K 0 0 0 rfl z hz (fun _ _ _ h => (Nat.not_lt_zero _ h).elim)
    obtain ⟨y, hy⟩ := rowBoundary K (hK 0 0) (componentAt K 0 ⟨(0, 0), rfl⟩ z) hc
    have hshape : (K.d 0 0).f 0 = 0 := by rw [K.shape _ _ (by decide)]; rfl
    rw [hshape] at hy
    change 0 = _ at hy
    have hz0 : z = 0 := totalComponent_ext_zero K z (fun a b hab => by
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a b
      exact hy.symm)
    exact ⟨0, (map_zero _).trans hz0.symm⟩
  | succ n =>
    obtain ⟨y, _, hy⟩ := removeAllRows K 0 (fun a b _ => hK a b) n z hz
      (fun _ _ _ h => (Nat.not_lt_zero _ h).elim)
    exact ⟨y, hy⟩

/-- 正の縦次数の行が完全なら、総複体から第 0 行への射影は擬同型。 -/
theorem totalToRowZero_quasiIso
    (hK : ∀ a b, 0 < b → (bicomplexRow K b).ExactAt a) : QuasiIso (totalToRowZero K) := by
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let hS := rowZeroShortExact K
  have hacyclic (j) := (rowZeroKernel_exact K hK j).isZero_homology
  have hm := (hS.homology_exact₂ i).mono_g_iff.mpr ((hacyclic i).eq_zero_of_src _)
  have he := (hS.homology_exact₃ i (i + 1) rfl).epi_f_iff.mpr
    ((hacyclic (i + 1)).eq_zero_of_tgt _)
  let : Mono (HomologicalComplex.homologyMap (totalToRowZero K) i) := hm
  let : Epi (HomologicalComplex.homologyMap (totalToRowZero K) i) := he
  exact isIso_of_mono_of_epi _

end SerrePositivity.HomologicalAlgebra
