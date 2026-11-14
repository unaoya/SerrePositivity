module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.RelativePDEnvelope
public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDAdicCompletion

/-!
# p 完備な相対分冪包

## 概要
基底の分冪と両立する p 完備分冪包の普遍性と存在。
BS 著者版 Theorem 5.2 の証明に現れる `D_J(P)` の環の部分。

## 方針
Berthelot I.2.3.1 の未完備包を p 進完備化し、有限冪商で分冪を延長する。

## 規約
完備性は古典的な `IsAdicComplete`。p ねじれに関する仮定を置かない。

## 使われ方
枠の分冪 Čech 脈体、分冪冪零化の塔。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

/-- 分冪イデアルを零に送る環射は、標的の零イデアルへの分冪射。 -/
theorem isDPMorphismToBot {B E : Type*} [CommRing B] [CommRing E]
    {I : Ideal B} (δ : DividedPowers I) (f : B →+* E) (hf : I ≤ RingHom.ker f) :
    δ.IsDPMorphism (dividedPowersBot E) f := by
  apply (DividedPowers.isDPMorphism_iff δ _ f).mpr
  exact ⟨Ideal.map_le_iff_le_comap.mpr hf, fun n hn x hx => by
    rw [RingHom.mem_ker.mp (hf hx), (dividedPowersBot E).dpow_eval_zero hn]
    exact (RingHom.mem_ker.mp (hf (δ.dpow_mem hn hx))).symm⟩

/-- 自然数 p が零の環は p 進完備。 -/
theorem isAdicComplete_of_natCast_zero {E : Type*} [CommRing E] {p : ℕ}
    (hp : (p : E) = 0) : IsAdicComplete (Ideal.span {(p : E)}) E := by
  rw [hp, Ideal.span_singleton_zero]
  exact IsAdicComplete.bot E

/-- 基底の分冪と両立する p 完備分冪包の普遍性。 -/
structure IsCompletedPDEnvelope (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k}
    (γ : DividedPowers J) {B : Type u} [CommRing B] [Algebra k B] (K : Ideal B)
    {D : Type u} [CommRing D] [Algebra k D] {K' : Ideal D}
    (δ : DividedPowers K') (η : B →ₐ[k] D) : Prop where
  /-- D は p 進完備。 -/
  complete : IsAdicComplete (Ideal.span {(p : D)}) D
  /-- K は K′ に入る。 -/
  map_le : K.map η ≤ K'
  /-- 基底の写像は分冪を保つ。 -/
  base_dp : DividedPowers.IsDPMorphism γ δ (algebraMap k D)
  /-- p 完備な標的への分冪を保つ延長の存在と一意性。 -/
  lift : ∀ {E : Type u} [CommRing E] [Algebra k E] {K'' : Ideal E} (ε : DividedPowers K''),
    IsAdicComplete (Ideal.span {(p : E)}) E → ∀ g : B →ₐ[k] E, K.map g ≤ K'' →
      DividedPowers.IsDPMorphism γ ε (algebraMap k E) →
      ∃! h : D →ₐ[k] E, DividedPowers.IsDPMorphism δ ε h.toRingHom ∧ h.comp η = g

namespace IsRelativePDEnvelope

variable {k B D : Type u} [CommRing k] [CommRing B] [CommRing D]
    [Algebra k B] [Algebra k D] {J : Ideal k} {γ : DividedPowers J}
    {K : Ideal B} {I : Ideal D} {δ : DividedPowers I} {η : B →ₐ[k] D}

variable (p : ℕ)
local notation "P" => Ideal.span {(p : D)}
local notation "C" => AdicCompletion P D
local notation "a" => (IsScalarTower.toAlgHom k D C)

/-- p の基底像は相対分冪包の分冪イデアルに属する。 -/
theorem prime_mem (h : IsRelativePDEnvelope γ K δ η) (hp : (p : k) ∈ J) :
    (p : D) ∈ I := by
  simpa only [map_natCast] using h.base_dp.ideal_comp (Ideal.mem_map_of_mem _ hp)

/-- p を含む基底上では、相対分冪包の p 進完備化は完備分冪包になる。 -/
theorem complete (h : IsRelativePDEnvelope γ K δ η) (hp : (p : k) ∈ J) :
    IsCompletedPDEnvelope p γ K (PDAdicCompletion.dividedPowers p δ (prime_mem p h hp))
      ((a).comp η) := by
  have ha := PDAdicCompletion.unit_isDPMorphism p δ (prime_mem p h hp)
  have hbase := ha.comp _ h.base_dp
  rw [← IsScalarTower.algebraMap_eq] at hbase
  refine ⟨PDAdicCompletion.isAdicComplete p, ?_, hbase, ?_⟩
  · change K.map ((a).toRingHom.comp η.toRingHom) ≤ _
    rw [← Ideal.map_map]
    exact (Ideal.map_mono h.map_le).trans ha.ideal_comp
  intro E _ _ L ε hE g hg hγ
  let := hE
  obtain ⟨f, hf, hunique⟩ := h.lift ε g hg hγ
  let : Algebra D E := f.toRingHom.toAlgebra
  let : IsScalarTower k D E := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let : IsScalarTower D E E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsAdicComplete P E := by
    apply (IsAdicComplete.map_algebraMap_iff (S := E) P E).mp
    have heq : (P).map (algebraMap D E) = Ideal.span {(p : E)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [heq]
    exact hE
  let hD : C →ₐ[D] E := adicCompletionToCompleteAlgebra D P (Submodule.fg_span_singleton _) E
  let F : C →ₐ[k] E := hD.restrictScalars k
  have hFa : F.comp a = f := AlgHom.ext hD.commutes
  have hFdp : DividedPowers.IsDPMorphism (PDAdicCompletion.dividedPowers p δ (prime_mem p h hp))
      ε F.toRingHom := by
    apply PDAdicCompletion.isDPMorphism_of_comp
    change DividedPowers.IsDPMorphism δ ε (F.comp a).toRingHom
    rw [hFa]
    exact hf.1
  refine ⟨F, ⟨hFdp, ?_⟩, ?_⟩
  · rw [← AlgHom.comp_assoc, hFa, hf.2]
  intro G hG
  have hGa : G.comp a = f := hunique _ ⟨hG.1.comp _ ha, by
    rw [AlgHom.comp_assoc, hG.2]⟩
  let gD : C →ₐ[D] E :=
    ⟨G.toRingHom, fun x => DFunLike.congr_fun hGa x⟩
  exact congrArg (AlgHom.restrictScalars k)
    (adicCompletion_algHom_ext D P (Submodule.fg_span_singleton _) E gD hD)

end IsRelativePDEnvelope

/-- 台環、分冪イデアルと標準脚を備えた p 完備分冪包。 -/
structure CompletedPDEnvelopeData (p : ℕ) {k : Type u} [CommRing k]
    {J : Ideal k} (γ : DividedPowers J) {B : Type u} [CommRing B] [Algebra k B]
    (K : Ideal B) where
  /-- 台環。 -/
  carrier : Type u
  /-- 台環の可換環構造。 -/
  [ring : CommRing carrier]
  /-- 基底の代数構造。 -/
  [algebra : Algebra k carrier]
  /-- 分冪イデアル。 -/
  ideal : Ideal carrier
  /-- 分冪。 -/
  dividedPowers : DividedPowers ideal
  /-- 入力環からの標準脚。 -/
  unit : B →ₐ[k] carrier
  /-- 標準脚の普遍性。 -/
  isEnvelope : IsCompletedPDEnvelope p γ K dividedPowers unit

attribute [instance] CompletedPDEnvelopeData.ring CompletedPDEnvelopeData.algebra

/-- 相対分冪包の p 完備化を、標準脚とともに取る。 -/
def completedPDEnvelope (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k}
    (γ : DividedPowers J) (hp : (p : k) ∈ J) {B : Type u} [CommRing B] [Algebra k B]
    (K : Ideal B) (hK : J.map (algebraMap k B) ≤ K) : CompletedPDEnvelopeData p γ K := by
  have h := (RelativePDEnvelope.isRelativePDEnvelope hK :
    IsRelativePDEnvelope γ K (RelativePDEnvelope.dividedPowers γ K) (RelativePDEnvelope.unit γ K))
  exact { carrier := _
          ideal := _
          dividedPowers := _
          unit := _
          isEnvelope := h.complete p hp }

/-- 任意の入力イデアルで、基底の分冪と両立する p 完備分冪包が存在する。
台環は入力環と同じ宇宙に属する。 -/
theorem exists_completedPDEnvelope (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k}
    (γ : DividedPowers J) (hp : (p : k) ∈ J) {B : Type u} [CommRing B] [Algebra k B]
    (K : Ideal B) (hK : J.map (algebraMap k B) ≤ K) :
    ∃ (D : Type u) (rc : CommRing D), letI := rc
      ∃ (ra : Algebra k D), letI := ra
        ∃ (K' : Ideal D) (δ : DividedPowers K') (η : B →ₐ[k] D),
          IsCompletedPDEnvelope p γ K δ η := by
  let D := completedPDEnvelope p γ hp K hK
  exact ⟨D.carrier, D.ring, D.algebra, D.ideal, D.dividedPowers, D.unit, D.isEnvelope⟩

namespace IsCompletedPDEnvelope

variable {p : ℕ} {k B D E : Type u} [CommRing k] [CommRing B] [CommRing D] [CommRing E]
    [Algebra k B] [Algebra k D] [Algebra k E] {J : Ideal k} {γ : DividedPowers J}
    {K : Ideal B} {I : Ideal D} {δ : DividedPowers I} {η : B →ₐ[k] D}
    {L : Ideal E} {ε : DividedPowers L}
variable (h : IsCompletedPDEnvelope p γ K δ η) (hE : IsAdicComplete (Ideal.span {(p : E)}) E)
    (g : B →ₐ[k] E) (hg : K.map g ≤ L) (he : γ.IsDPMorphism ε (algebraMap k E))

/-- 普遍性から取った分冪を保つ代数射。 -/
def liftHom : D →ₐ[k] E := (h.lift ε hE g hg he).exists.choose

/-- 普遍性の射は分冪を保つ。 -/
theorem liftHom_isDPMorphism : δ.IsDPMorphism ε (h.liftHom hE g hg he).toRingHom :=
  (h.lift ε hE g hg he).exists.choose_spec.1

/-- 普遍性の射と標準脚の合成は指定した代数射。 -/
@[simp] theorem liftHom_comp : (h.liftHom hE g hg he).comp η = g :=
  (h.lift ε hE g hg he).exists.choose_spec.2

include h hE in
/-- 完備分冪包からの二つの分冪射は標準脚との合成で決まる。 -/
theorem hom_ext {f₁ f₂ : D →ₐ[k] E}
    (h₁ : δ.IsDPMorphism ε f₁.toRingHom) (h₂ : δ.IsDPMorphism ε f₂.toRingHom)
    (hf : f₁.comp η = f₂.comp η) : f₁ = f₂ := by
  have hm : K.map (f₂.comp η) ≤ L := by
    change K.map (f₂.toRingHom.comp η.toRingHom) ≤ L
    rw [← Ideal.map_map]
    exact (Ideal.map_mono h.map_le).trans h₂.ideal_comp
  have hb := h₂.comp _ h.base_dp
  have hc : f₂.toRingHom.comp (algebraMap k D) = algebraMap k E :=
    RingHom.ext f₂.commutes
  rw [hc] at hb
  exact (h.lift ε hE (f₂.comp η) hm hb).unique ⟨h₁, hf⟩ ⟨h₂, rfl⟩

section Quotient

variable (hp : (p : k) ∈ J) (hK : J.map (algebraMap k B) ≤ K)

include hK in
private theorem quotient_base_mem (x : k) (hx : x ∈ J) :
    algebraMap k B x ∈ K := hK (Ideal.mem_map_of_mem _ hx)

include h in
private theorem quotient_ideal_mem (x : k) (hx : x ∈ J) :
    algebraMap k D x ∈ I := h.base_dp.ideal_comp (Ideal.mem_map_of_mem _ hx)

/-- 完備分冪包を分冪イデアルで割ると入力環の剰余環に戻る。 -/
def quotientEquiv : (D ⧸ I) ≃ₐ[k] (B ⧸ K) := by
  let qB := Ideal.Quotient.mkₐ k K
  let qD := Ideal.Quotient.mkₐ k I
  have hk : J ≤ RingHom.ker (algebraMap k (B ⧸ K)) := by
    intro x hx
    change Ideal.Quotient.mk K (algebraMap k B x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (quotient_base_mem hK x hx)
  have hpB : (p : B ⧸ K) = 0 := by simpa only [map_natCast] using RingHom.mem_ker.mp (hk hp)
  have hpD : (p : D ⧸ I) = 0 := by
    have hz : Ideal.Quotient.mk I (algebraMap k D (p : k)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (quotient_ideal_mem h (p : k) hp)
    simpa only [map_natCast] using hz
  let F := h.liftHom (ε := dividedPowersBot (B ⧸ K)) (isAdicComplete_of_natCast_zero hpB)
    qB (Ideal.map_le_iff_le_comap.mpr fun _ hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx)
    (isDPMorphismToBot γ _ hk)
  have hF : δ.IsDPMorphism (dividedPowersBot (B ⧸ K)) F.toRingHom :=
    h.liftHom_isDPMorphism ..
  have hFu : F.comp η = qB := h.liftHom_comp ..
  let f := Ideal.Quotient.liftₐ I F (fun x hx =>
    hF.ideal_comp (Ideal.mem_map_of_mem F hx))
  let g := Ideal.Quotient.liftₐ K (qD.comp η) (fun x hx =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (h.map_le (Ideal.mem_map_of_mem η hx)))
  have hgc : g.comp F = qD := by
    apply h.hom_ext (isAdicComplete_of_natCast_zero hpD)
      (isDPMorphismToBot δ _ (fun x hx => by
        change g (F x) = 0
        rw [show F x = 0 from hF.ideal_comp (Ideal.mem_map_of_mem F hx), map_zero]))
      (isDPMorphismToBot δ qD.toRingHom fun _ hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx)
    rw [AlgHom.comp_assoc, hFu]
    rfl
  refine AlgEquiv.ofAlgHom f g (Ideal.Quotient.algHom_ext k ?_)
    (Ideal.Quotient.algHom_ext k ?_)
  · ext1 x
    exact DFunLike.congr_fun hFu x
  · ext1 x
    exact DFunLike.congr_fun hgc x

/-- 剰余環の同型は標準脚で入力環の商写像に一致する。 -/
@[simp] theorem quotientEquiv_mk_unit (x : B) :
    h.quotientEquiv hp hK (Ideal.Quotient.mk I (η x)) = Ideal.Quotient.mk K x := by
  unfold quotientEquiv
  exact DFunLike.congr_fun (h.liftHom_comp ..) x

end Quotient

end IsCompletedPDEnvelope

end SerrePositivity.BhattScholze.Prismatic
