module

public import SerrePositivity.BhattScholze.Delta.DeltaAdicExtension
public import SerrePositivity.BhattScholze.Delta.DeltaIdentities
public import SerrePositivity.CommutativeAlgebra.AdicCompletionQuotient

/-! # 古典的I進完備化のδ構造

著者公開版Lemma 2.17の存在部分。Mathlibの古典的完備化上に構成したδ写像が
δ恒等式を満たすことを有限商の座標で確認する。導来完備化への置換ではない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
open AdicCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

private theorem exists_successor_representative (I : Ideal R) (n : ℕ)
    (x : AdicCompletion I R) : ∃ r : R,
      evalₐ I (n + 1) x = Ideal.Quotient.mk (I ^ (n + 1)) r ∧
      evalₐ I n x = Ideal.Quotient.mk (I ^ n) r := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I R x
  refine ⟨f (n + 1), by rw [evalₐ_mk], ?_⟩
  rw [evalₐ_mk]
  simpa [SModEq.def, smul_eq_mul] using f.property (Nat.le_succ n)

/-- 完備化上のδ写像は積公式を満たす。 -/
theorem adicDeltaExtension_mul (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (x y : AdicCompletion I R) :
    D.adicDeltaExtension I hp (x * y) =
      x ^ p * D.adicDeltaExtension I hp y + D.adicDeltaExtension I hp x * y ^ p +
        (p : AdicCompletion I R) * D.adicDeltaExtension I hp x * D.adicDeltaExtension I hp y := by
  apply ext_evalₐ
  intro n
  obtain ⟨a, ha, ha'⟩ := exists_successor_representative I n x
  obtain ⟨b, hb, hb'⟩ := exists_successor_representative I n y
  rw [D.eval_adicDeltaExtension, map_mul, ha, hb, ← map_mul,
    D.adicDeltaStep_mk I hp, D.delta_mul]
  simp only [map_add, map_mul, map_pow, map_natCast]
  rw [D.eval_adicDeltaExtension, D.eval_adicDeltaExtension, ha, hb,
    D.adicDeltaStep_mk I hp, D.adicDeltaStep_mk I hp, ha', hb']

/-- 完備化上のδ写像はWitt繰上りを含む加法公式を満たす。 -/
theorem adicDeltaExtension_add (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (x y : AdicCompletion I R) :
    D.adicDeltaExtension I hp (x + y) =
      D.adicDeltaExtension I hp x + D.adicDeltaExtension I hp y +
        (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 := by
  apply ext_evalₐ
  intro n
  obtain ⟨a, ha, ha'⟩ := exists_successor_representative I n x
  obtain ⟨b, hb, hb'⟩ := exists_successor_representative I n y
  rw [D.eval_adicDeltaExtension, map_add, ha, hb, ← map_add, D.adicDeltaStep_mk I hp,
    D.delta_add]
  simp only [map_add, D.eval_adicDeltaExtension, ha, hb, D.adicDeltaStep_mk I hp]
  congr 1
  rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
    WittVector.map_teichmuller]
  symm
  change (evalₐ I n).toRingHom
    ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1) = _
  rw [← WittVector.map_coeff (evalₐ I n).toRingHom, map_add, WittVector.map_teichmuller,
    WittVector.map_teichmuller]
  change (WittVector.teichmuller p (evalₐ I n x) +
    WittVector.teichmuller p (evalₐ I n y)).coeff 1 = _
  rw [ha', hb']

/-- pを含む任意のイデアルの古典的完備化のδ構造。
存在の構成に有限生成性・p正則性は不要。 -/
def adicCompletion (D : DeltaStructure p R) (I : Ideal R) (hp : (p : R) ∈ I) :
    DeltaStructure p (AdicCompletion I R) :=
  ofFunction (D.adicDeltaExtension I hp)
    (by have h := D.adicDeltaExtension_of I hp 0
        rw [D.delta_zero, _root_.map_zero] at h
        exact h)
    (by have h := D.adicDeltaExtension_of I hp 1
        rw [D.delta_one, _root_.map_zero] at h
        exact h)
    (D.adicDeltaExtension_add I hp) (D.adicDeltaExtension_mul I hp)

/-- 完備化δ構造のδは構成した座標延長に等しい。 -/
@[simp] theorem adicCompletion_delta (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (x : AdicCompletion I R) :
    (D.adicCompletion I hp).delta x = D.adicDeltaExtension I hp x := rfl

/-- 基底から古典的完備化への標準環射はδ射。 -/
theorem isDeltaHom_adicCompletion (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) :
    D.IsDeltaHom (D.adicCompletion I hp) (algebraMap R (AdicCompletion I R)) := by
  intro x
  exact (D.adicDeltaExtension_of I hp x).symm

/-- Iが有限生成なら、標準射と両立する古典的完備化のδ構造は一意。
共通層の評価核と拡張イデアル冪の一致を使用する。 -/
theorem adicCompletion_unique (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (hI : I.FG) (E : DeltaStructure p (AdicCompletion I R))
    (hE : D.IsDeltaHom E (algebraMap R (AdicCompletion I R))) :
    E = D.adicCompletion I hp := by
  apply ext
  intro x
  apply ext_evalₐ
  intro n
  obtain ⟨r, hr, _⟩ := exists_successor_representative I n x
  let f := algebraMap R (AdicCompletion I R)
  let J := I.map f
  have hpJ : (p : AdicCompletion I R) ∈ J := by
    simpa only [map_natCast] using Ideal.mem_map_of_mem f hp
  have hxJ : x - f r ∈ J ^ (n + 1) := by
    rw [← SerrePositivity.adicCompletion_ker_eval_eq_pow_map I hI]
    change evalₐ I (n + 1) (x - f r) = 0
    rw [map_sub, hr]
    change Ideal.Quotient.mk _ r - Ideal.Quotient.mk _ r = 0
    exact sub_self _
  have he := E.delta_sub_mem_pow J hpJ n x (f r) hxJ
  have he' : evalₐ I n (E.delta x - E.delta (f r)) = 0 := by
    change E.delta x - E.delta (f r) ∈ RingHom.ker (evalₐ I n).toRingHom
    rw [SerrePositivity.adicCompletion_ker_eval_eq_pow_map I hI]
    exact he
  rw [map_sub, ← hE r] at he'
  rw [adicCompletion_delta, D.eval_adicDeltaExtension, hr, D.adicDeltaStep_mk I hp]
  exact sub_eq_zero.mp he'

/-- pを含む有限生成イデアルの古典的完備化は、一意な適合δ構造を持つ。
著者公開版Lemma 2.17の存在・一意性。 -/
theorem existsUnique_adicCompletion (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (hI : I.FG) :
    ∃! E : DeltaStructure p (AdicCompletion I R),
      D.IsDeltaHom E (algebraMap R (AdicCompletion I R)) :=
  ⟨D.adicCompletion I hp, D.isDeltaHom_adicCompletion I hp,
    fun E hE ↦ D.adicCompletion_unique I hp hI E hE⟩

end SerrePositivity.BhattScholze.DeltaStructure
