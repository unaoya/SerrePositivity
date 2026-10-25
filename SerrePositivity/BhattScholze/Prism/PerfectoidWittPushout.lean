module

public import SerrePositivity.BhattScholze.Prism.WittCoefficientPushout
public import SerrePositivity.BhattScholze.Prism.WittDistinguishedQuotientPerfectoid

/-! # B4-5：共通生成元によるWitt商の余積

完全係数環のテンソルのWitt環を、基底の生成元の像で割る。
係数テンソルが零環になる場合も含めて、候補のperfectoid性と
p完備試験環への普遍性を証明する。導来テンソルの比較とは区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] (R A B : Type u)
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- 基底Witt元の像で係数テンソルのWitt環を割った環。 -/
abbrev WittCoefficientPushout (d : WittVector p R) :=
  WittVector p (A ⊗[R] B) ⧸ Ideal.span
    {WittVector.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
      (WittVector.map (algebraMap R A) d)}

/-- 左因子のWitt商からの標準射。 -/
def wittCoefficientPushoutLeft (d : WittVector p R) :
    (WittVector p A ⧸ Ideal.span {WittVector.map (algebraMap R A) d}) →+*
      WittCoefficientPushout p R A B d := by
  let q : WittVector p (A ⊗[R] B) →+* WittCoefficientPushout p R A B d :=
    Ideal.Quotient.mk _
  let f := q.comp
    (WittVector.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom)
  have hk : Ideal.span {WittVector.map (algebraMap R A) d} ≤ RingHom.ker f := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  exact Ideal.Quotient.lift _ f (fun _ hx ↦ hk hx)

/-- 右因子のWitt商からの標準射。 -/
def wittCoefficientPushoutRight (d : WittVector p R) :
    (WittVector p B ⧸ Ideal.span {WittVector.map (algebraMap R B) d}) →+*
      WittCoefficientPushout p R A B d := by
  let q : WittVector p (A ⊗[R] B) →+* WittCoefficientPushout p R A B d :=
    Ideal.Quotient.mk _
  let f := q.comp
    (WittVector.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)
  have hk : Ideal.span {WittVector.map (algebraMap R B) d} ≤ RingHom.ker f := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change Ideal.Quotient.mk _
      (WittVector.map _ (WittVector.map _ d)) = 0
    have he := RingHom.congr_fun (wittCoefficientTensor_base_agreement p (R := R)
      (A := A) (B := B)) d
    change WittVector.map _ (WittVector.map _ d) =
      WittVector.map _ (WittVector.map _ d) at he
    rw [← he]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  exact Ideal.Quotient.lift _ f (fun _ hx ↦ hk hx)

/-- 左標準射のWitt代表元上の式。 -/
@[simp] theorem wittCoefficientPushoutLeft_mk (d : WittVector p R) (x : WittVector p A) :
    wittCoefficientPushoutLeft p R A B d (Ideal.Quotient.mk _ x) =
    Ideal.Quotient.mk _
      (WittVector.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom x) := rfl

/-- 右標準射のWitt代表元上の式。 -/
@[simp] theorem wittCoefficientPushoutRight_mk (d : WittVector p R) (x : WittVector p B) :
    wittCoefficientPushoutRight p R A B d (Ideal.Quotient.mk _ x) =
    Ideal.Quotient.mk _
      (WittVector.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom x) := rfl

/-- 標準射は基底Witt環上で一致する。 -/
theorem wittCoefficientPushout_base_agreement (d : WittVector p R) :
    ((wittCoefficientPushoutLeft p R A B d).comp (Ideal.Quotient.mk _)).comp
      (WittVector.map (algebraMap R A)) =
    ((wittCoefficientPushoutRight p R A B d).comp (Ideal.Quotient.mk _)).comp
      (WittVector.map (algebraMap R B)) := by
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, wittCoefficientPushoutLeft_mk,
    wittCoefficientPushoutRight_mk]
  exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun
    (wittCoefficientTensor_base_agreement p (R := R) (A := A) (B := B)) x)

variable [CharP R p] [CharP A p] [CharP B p]
variable [PerfectRing R p] [PerfectRing A p] [PerfectRing B p]

/-- 共通distinguished元によるWitt係数余積はperfectoid。零環の係数テンソルも含む。 -/
theorem wittCoefficientPushout_isIntegralPerfectoid (d : WittVector p R)
    (hd : (wittDeltaStructure p R).IsDistinguished d) :
    IsIntegralPerfectoid (WittCoefficientPushout p R A B d) p := by
  let K := A ⊗[R] B
  rcases subsingleton_or_nontrivial K with hK | hK
  · let := hK
    have : Subsingleton (WittVector p K) := ⟨fun x y ↦ by
      apply WittVector.ext
      intro n
      exact Subsingleton.elim _ _⟩
    exact Or.inl inferInstance
  · let := hK
    have hp : (p : K) = 0 := by
      rw [← map_natCast (algebraMap R K), CharP.cast_eq_zero, map_zero]
    let : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    let : PerfectRing K p := perfectCoefficientTensor_perfectRing p R A B
    have hA := (wittDeltaStructure_map_isDeltaHom p R (algebraMap R A)).map_isDistinguished hd
    have hK := (wittDeltaStructure_map_isDeltaHom p A
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom).map_isDistinguished hA
    exact wittDistinguishedQuotient_isIntegralPerfectoid p K _ hK

/-- 両因子の共通生成元によるWitt商の射は、p完備な試験環へ一意に延長する。
試験環のp正則性・非零性は要求しない。 -/
theorem existsUnique_wittCoefficientPushoutLift (d : WittVector p R)
    {D : Type u} [CommRing D] [IsAdicComplete (Ideal.span {(p : D)}) D]
    (f : (WittVector p A ⧸ Ideal.span {WittVector.map (algebraMap R A) d}) →+* D)
    (g : (WittVector p B ⧸ Ideal.span {WittVector.map (algebraMap R B) d}) →+* D)
    (h : (f.comp (Ideal.Quotient.mk _)).comp (WittVector.map (algebraMap R A)) =
      (g.comp (Ideal.Quotient.mk _)).comp (WittVector.map (algebraMap R B))) :
    ∃! L : WittCoefficientPushout p R A B d →+* D,
      L.comp (wittCoefficientPushoutLeft p R A B d) = f ∧
      L.comp (wittCoefficientPushoutRight p R A B d) = g := by
  obtain ⟨L, ⟨hA, hB⟩, huniq⟩ := existsUnique_wittCoefficientTensorLift_of_perfect p
    (f.comp (Ideal.Quotient.mk _)) (g.comp (Ideal.Quotient.mk _)) h
  let e := WittVector.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
    (WittVector.map (algebraMap R A) d)
  have hzero : L e = 0 := by
    have he := RingHom.congr_fun hA (WittVector.map (algebraMap R A) d)
    change L e = f (Ideal.Quotient.mk _ _) at he
    have hz : Ideal.Quotient.mk (Ideal.span {WittVector.map (algebraMap R A) d})
      (WittVector.map (algebraMap R A) d) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [he, hz, map_zero]
  have hk : Ideal.span {e} ≤ RingHom.ker L := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact hzero
  let M := Ideal.Quotient.lift (Ideal.span {e}) L (fun _ hx ↦ hk hx)
  have hMA : M.comp (wittCoefficientPushoutLeft p R A B d) = f := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    exact RingHom.congr_fun hA x
  have hMB : M.comp (wittCoefficientPushoutRight p R A B d) = g := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    exact RingHom.congr_fun hB x
  refine ⟨M, ⟨hMA, hMB⟩, ?_⟩
  intro N hN
  apply Ideal.Quotient.ringHom_ext
  change N.comp (Ideal.Quotient.mk _) = L
  apply huniq
  constructor
  · apply RingHom.ext
    intro x
    exact RingHom.congr_fun hN.1 (Ideal.Quotient.mk _ x)
  · apply RingHom.ext
    intro x
    exact RingHom.congr_fun hN.2 (Ideal.Quotient.mk _ x)

end SerrePositivity.BhattScholze
