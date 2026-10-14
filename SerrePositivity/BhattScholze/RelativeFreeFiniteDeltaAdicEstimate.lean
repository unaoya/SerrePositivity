module

public import SerrePositivity.BhattScholze.RelativeFreeFiniteDeltaStepIdentities
public import SerrePositivity.BhattScholze.DeltaAdicEstimate
public import Mathlib.RingTheory.Ideal.Maps

/-! # 異なる有限段の間のδ計算のイデアル冪評価

次段イデアルJと初期包含の逆像について、有限δ計算で失う冪を追う。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 次段のJがpを含むなら、逆像のm+1乗の有限δ像はJのm乗に入る。 -/
theorem relativeFreeFiniteDeltaStep_mem_pow (D : DeltaStructure p A)
    (J : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hp : (p : MvPolynomial (σ × Fin (N + 2)) A) ∈ J)
    (m : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A)
    (hf : f ∈ (J.comap (relativeFreeFiniteStepInclusion N σ)) ^ (m + 1)) :
    relativeFreeFiniteDeltaStep N σ D f ∈ J ^ m := by
  let I := J.comap (relativeFreeFiniteStepInclusion N σ)
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    have hmul : f ∈ (I ^ (m + 1)) * I := by simpa only [I, pow_succ] using hf
    have he : relativeFreeFiniteStepInclusion N σ f ∈ J ^ (m + 1) ∧
        relativeFreeFiniteDeltaStep N σ D f ∈ J ^ (m + 1) := by
      refine Submodule.mul_induction_on (C := fun z =>
        relativeFreeFiniteStepInclusion N σ z ∈ J ^ (m + 1) ∧
          relativeFreeFiniteDeltaStep N σ D z ∈ J ^ (m + 1)) hmul ?_ ?_
      · intro a ha b hb
        have ha' : relativeFreeFiniteStepInclusion N σ a ∈ J ^ (m + 1) :=
          Ideal.le_comap_pow (relativeFreeFiniteStepInclusion N σ) (m + 1) ha
        have hb' : relativeFreeFiniteStepInclusion N σ b ∈ J := hb
        constructor
        · rw [map_mul]
          exact (J ^ (m + 1)).mul_mem_right _ ha'
        · rw [relativeFreeFiniteDeltaStep_mul]
          apply (J ^ (m + 1)).add_mem
          · apply (J ^ (m + 1)).add_mem
            · exact (J ^ (m + 1)).mul_mem_right _
                ((J ^ (m + 1)).pow_mem_of_mem ha' p (Fact.out : p.Prime).pos)
            · have hprod := Ideal.mul_mem_mul (ih a ha)
                (J.pow_mem_of_mem hb' p (Fact.out : p.Prime).pos)
              simpa only [pow_succ] using hprod
          · have hprod := Ideal.mul_mem_mul (ih a ha) hp
            have hprod' : relativeFreeFiniteDeltaStep N σ D a *
                (p : MvPolynomial (σ × Fin (N + 2)) A) ∈ J ^ (m + 1) := by
              simpa only [pow_succ] using hprod
            simpa only [mul_comm, mul_left_comm, mul_assoc] using
              (J ^ (m + 1)).mul_mem_right (relativeFreeFiniteDeltaStep N σ D b) hprod'
      · intro a b ha hb
        constructor
        · rw [map_add]
          exact (J ^ (m + 1)).add_mem ha.1 hb.1
        · rw [relativeFreeFiniteDeltaStep_add]
          exact (J ^ (m + 1)).add_mem ((J ^ (m + 1)).add_mem ha.2 hb.2)
            (wittAdditionCarry_mem_of_right_mem (J ^ (m + 1)) _ _ hb.1)
    exact he.2

/-- 逆像のm+1乗に属す摂動による有限δ像の変化はJのm乗に入る。 -/
theorem relativeFreeFiniteDeltaStep_add_sub_mem_pow (D : DeltaStructure p A)
    (J : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hp : (p : MvPolynomial (σ × Fin (N + 2)) A) ∈ J)
    (m : ℕ) (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hg : g ∈ (J.comap (relativeFreeFiniteStepInclusion N σ)) ^ (m + 1)) :
    relativeFreeFiniteDeltaStep N σ D (f + g) - relativeFreeFiniteDeltaStep N σ D f ∈
      J ^ m := by
  have hg' : relativeFreeFiniteStepInclusion N σ g ∈ J ^ (m + 1) :=
    Ideal.le_comap_pow (relativeFreeFiniteStepInclusion N σ) (m + 1) hg
  have hc := wittAdditionCarry_mem_of_right_mem (p := p) (J ^ (m + 1))
    (relativeFreeFiniteStepInclusion N σ f) (relativeFreeFiniteStepInclusion N σ g) hg'
  have he := (J ^ m).add_mem (relativeFreeFiniteDeltaStep_mem_pow N σ D J hp m g hg)
    (Ideal.pow_le_pow_right (by omega : m ≤ m + 1) hc)
  rw [relativeFreeFiniteDeltaStep_add]
  convert he using 1
  ring

/-- 二代表元が逆像のm+1乗まで一致すれば有限δ像はJのm乗まで一致する。 -/
theorem relativeFreeFiniteDeltaStep_sub_mem_pow (D : DeltaStructure p A)
    (J : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hp : (p : MvPolynomial (σ × Fin (N + 2)) A) ∈ J)
    (m : ℕ) (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hfg : f - g ∈ (J.comap (relativeFreeFiniteStepInclusion N σ)) ^ (m + 1)) :
    relativeFreeFiniteDeltaStep N σ D f - relativeFreeFiniteDeltaStep N σ D g ∈ J ^ m := by
  have he := relativeFreeFiniteDeltaStep_add_sub_mem_pow N σ D J hp m g (f - g) hfg
  simpa only [add_sub_cancel] using he

end SerrePositivity.BhattScholze
