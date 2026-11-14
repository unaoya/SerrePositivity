module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech

/-!
# 小さい完備分冪模型と枠の比較

## 概要
Theorem 5.2 の小さい分冪模型を、第零頂点と頂点差からなる枠の完備分冪包に同定する。

## 方針
未完備包の普遍性を p 進完備化し、p 正則性で Theorem 5.2 の主完備化と比較する。
余単体自然性は、完備化の前に枠の変数上で確かめて延長する。

## 規約
枠の添字は係数環と同じ宇宙で取るため `ULift (Fin r)` を用いる。
正則性の仮定は係数環に置く。

## 使われ方
BS 著者版 Theorem 5.2 の小さい多項式分冪模型の比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

namespace IsCompletedPDEnvelope

variable {p : ℕ} {k B D E : Type u} [CommRing k] [CommRing B] [CommRing D] [CommRing E]
  [Algebra k B] [Algebra k D] [Algebra k E] {J : Ideal k} {γ : DividedPowers J}
  {K : Ideal B} {I : Ideal D} {δ : DividedPowers I} {η : B →ₐ[k] D}
  {L : Ideal E} {ε : DividedPowers L} {ι : B →ₐ[k] E}
variable (h : IsCompletedPDEnvelope p γ K δ η) (h' : IsCompletedPDEnvelope p γ K ε ι)

/-- 同じ入力の完備分冪包の標準同型。 -/
def equiv : D ≃ₐ[k] E := by
  let f := h.liftHom h'.complete ι h'.map_le h'.base_dp
  let g := h'.liftHom h.complete η h.map_le h.base_dp
  have hf : δ.IsDPMorphism ε f.toRingHom := h.liftHom_isDPMorphism ..
  have hg : ε.IsDPMorphism δ g.toRingHom := h'.liftHom_isDPMorphism ..
  have hfu : f.comp η = ι := h.liftHom_comp ..
  have hgu : g.comp ι = η := h'.liftHom_comp ..
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply h'.hom_ext h'.complete (hf.comp _ hg) (DividedPowers.DPMorphism.id ε).isDPMorphism
    rw [AlgHom.comp_assoc, hgu, hfu, AlgHom.id_comp]
  · apply h.hom_ext h.complete (hg.comp _ hf) (DividedPowers.DPMorphism.id δ).isDPMorphism
    rw [AlgHom.comp_assoc, hfu, hgu, AlgHom.id_comp]

/-- 同型は標準脚を保つ。 -/
theorem equiv_unit (x : B) : h.equiv h' (η x) = ι x :=
  DFunLike.congr_fun (h.liftHom_comp ..) x

/-- 同型の環射は分冪を保つ。 -/
theorem equiv_isDPMorphism : δ.IsDPMorphism ε (h.equiv h').toRingHom :=
  h.liftHom_isDPMorphism ..

end IsCompletedPDEnvelope

namespace PDSmallModelComparison

private def toAdicCompletion (p : ℕ) (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] :
    R →ₐ[k] AdicCompletion (Ideal.span {(p : R)}) R :=
  IsScalarTower.toAlgHom k R _

private def principalAdicRingEquiv (R : Type u) [CommRing R] (a : R)
    (ha : IsSMulRegular R a) :
    letI := principalCompletionCommRing R a
    PrincipalCompletionH0 R a ≃+* AdicCompletion (Ideal.span {a}) R := by
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  exact (principalCompletionAdicAlgEquiv R a ha).toRingEquiv

private theorem principalAdicRingEquiv_unit (R : Type u) [CommRing R] (a : R)
    (ha : IsSMulRegular R a) (x : R) :
    letI := principalCompletionCommRing R a
    principalAdicRingEquiv R a ha (principalCompletionUnitRingHom R a x) =
      algebraMap R (AdicCompletion (Ideal.span {a}) R) x :=
  principalCompletionAdicAlgEquiv_unit R a ha x

private theorem complete_of_ringHom {R T : Type u} [CommRing R] [CommRing T]
    (p : ℕ) (a : R →+* T) (hT : IsAdicComplete (Ideal.span {(p : T)}) T) :
    letI := a.toAlgebra
    IsModuleComplete R (p : R) (ModuleCat.of R T) := by
  let := a.toAlgebra
  let : IsScalarTower R T T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let h : IsAdicComplete (Ideal.span {(p : R)}) T := by
    apply (IsAdicComplete.map_algebraMap_iff (S := T) (Ideal.span {(p : R)}) T).mp
    have he : (Ideal.span {(p : R)}).map (algebraMap R T) = Ideal.span {(p : T)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [he]
    exact hT
  exact @isModuleComplete_of_isAdicComplete R _ (p : R) (ModuleCat.of R T) h

variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] {J : Ideal k}
variable (γ : DividedPowers J) (hp : (p : k) ∈ J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hreg : Function.Injective (fun x : k => (p : k) * x)) (r : ℕ)
variable (hJ : J ≤ RingHom.ker (algebraMap k (MvPolynomial (Fin r) (k ⧸ J))))

local notation "s" => (fun j : ULift (Fin r) =>
  (MvPolynomial.X (ULift.down j) : MvPolynomial (Fin r) (k ⧸ J)))
local notation "FrameTerm" => PDCechNerve.term p γ hp hJ s
local notation "Raw" => pdRaw k r
local notation "Comp" => fun n : ℕ => AdicCompletion (Ideal.span {(p : Raw n)}) (Raw n)
local notation "E" => pdModel p k r
local notation "N" => pdCechNerve p γ hp hJ s

private def adicEquiv (n : ℕ) :
    AdicCompletion (Ideal.span {(p : Raw n)}) (Raw n) ≃ₐ[k] (FrameTerm n).carrier :=
  ((PDSmallRawEnvelope.isRelativePDEnvelope p r n γ hk hreg).complete p hp).equiv
    (FrameTerm n).isEnvelope

private def rawToFrame (n : ℕ) : Raw n →ₐ[k] (FrameTerm n).carrier :=
  (adicEquiv p k γ hp hk hreg r hJ n).toAlgHom.comp (toAdicCompletion p k (Raw n))

private theorem rawToFrame_isDPMorphism (n : ℕ) :
    (PDSmallRawEnvelope.dividedPowers p r n γ hk hreg).IsDPMorphism
      (FrameTerm n).dividedPowers (rawToFrame p k γ hp hk hreg r hJ n).toRingHom := by
  have h := PDSmallRawEnvelope.isRelativePDEnvelope p r n γ hk hreg
  have hu := PDAdicCompletion.unit_isDPMorphism (R := Raw n) p
    (PDSmallRawEnvelope.dividedPowers p r n γ hk hreg) (h.prime_mem p hp)
  exact ((h.complete p hp).equiv_isDPMorphism (FrameTerm n).isEnvelope).comp _ hu

@[simp] private theorem rawToFrame_unit (n : ℕ) (x : pdFrame k (ULift.{u} (Fin r)) n) :
    rawToFrame p k γ hp hk hreg r hJ n (PDSmallRawEnvelope.unit r n x) = (FrameTerm n).unit x :=
  IsCompletedPDEnvelope.equiv_unit
    ((PDSmallRawEnvelope.isRelativePDEnvelope p r n γ hk hreg).complete p hp)
    (FrameTerm n).isEnvelope x

private def termEquiv (n : ℕ) : pdTerm p k r n ≃ₐ[k] (FrameTerm n).carrier := by
  let c : pdTerm p k r n ≃+* Comp n := principalAdicRingEquiv (Raw n) (p : Raw n)
    (PDSmallRawEnvelope.raw_regular p r n hreg)
  let d := adicEquiv p k γ hp hk hreg r hJ n
  refine { c.trans d.toRingEquiv with commutes' := fun x => ?_ }
  change d (c (principalCompletionUnitRingHom (Raw n) (p : Raw n) (algebraMap k (Raw n) x))) = _
  have hc := principalAdicRingEquiv_unit (Raw n) (p : Raw n)
    (PDSmallRawEnvelope.raw_regular p r n hreg) (algebraMap k (Raw n) x)
  exact (congrArg d hc).trans (d.commutes x)

private theorem termEquiv_unit (n : ℕ) (x : Raw n) :
    termEquiv p k γ hp hk hreg r hJ n (principalCompletionUnitRingHom (Raw n) (p : Raw n) x) =
      rawToFrame p k γ hp hk hreg r hJ n x := by
  change adicEquiv p k γ hp hk hreg r hJ n
    (principalAdicRingEquiv (Raw n) (p : Raw n) _ (principalCompletionUnitRingHom _ _ x)) =
      adicEquiv p k γ hp hk hreg r hJ n (toAdicCompletion p k (Raw n) x)
  exact congrArg (adicEquiv p k γ hp hk hreg r hJ n)
    (principalAdicRingEquiv_unit (Raw n) (p : Raw n)
      (PDSmallRawEnvelope.raw_regular p r n hreg) x)

private theorem rawToFrame_natural {m n : SimplexCategory} (θ : m ⟶ n) :
    (rawToFrame p k γ hp hk hreg r hJ n.len).toRingHom.comp ((pdRawModel k r).map θ).right.hom =
      ((N).map θ).right.hom.comp (rawToFrame p k γ hp hk hreg r hJ m.len).toRingHom := by
  -- 未完備の比較は枠の変数の像で決まる。
  let A := rawToFrame p k γ hp hk hreg r hJ
  let M := PDCechNerve.mapCopies p γ hp hJ s θ.toOrderHom
  let f := pdRawMap k r θ
  have h₁ := (rawToFrame_isDPMorphism p k γ hp hk hreg r hJ n.len).comp _
    (PDSmallRawEnvelope.map_isDPMorphism p r γ hk hreg θ)
  have h₂ := (PDCechNerve.mapCopies_isDPMorphism p γ hp hJ s θ.toOrderHom).comp _
    (rawToFrame_isDPMorphism p k γ hp hk hreg r hJ m.len)
  have he : (A n.len).comp f = M.comp (A m.len) := by
    have h := (PDSmallRawEnvelope.isRelativePDEnvelope p r m.len γ hk hreg).lift
      (FrameTerm n.len).dividedPowers (M.comp ((FrameTerm m.len).unit))
      (by
        change Ideal.map (M.toRingHom.comp ((FrameTerm m.len).unit).toRingHom) _ ≤ _
        rw [← Ideal.map_map]
        exact (Ideal.map_mono (FrameTerm m.len).isEnvelope.map_le).trans
          (PDCechNerve.mapCopies_isDPMorphism p γ hp hJ s θ.toOrderHom).ideal_comp)
      (FrameTerm n.len).isEnvelope.base_dp
    refine h.unique ⟨h₁, ?_⟩ ⟨h₂, ?_⟩
    · apply MvPolynomial.algHom_ext
      intro x
      change rawToFrame p k γ hp hk hreg r hJ n.len
          (pdRawMap k r θ (PDSmallRawEnvelope.unit r m.len (MvPolynomial.X x))) =
        M ((FrameTerm m.len).unit (MvPolynomial.X x))
      rw [PDSmallRawEnvelope.map_unit, rawToFrame_unit]
      exact (PDCechNerve.mapCopies_variableImage p γ hp hJ s θ.toOrderHom x).symm
    · apply AlgHom.ext
      intro x
      change M (rawToFrame p k γ hp hk hreg r hJ m.len (PDSmallRawEnvelope.unit r m.len x)) =
        M ((FrameTerm m.len).unit x)
      rw [rawToFrame_unit]
  exact congrArg AlgHom.toRingHom he

private def termIso (n : SimplexCategory) : (E).obj n ≅ (N).obj n :=
  Under.isoMk ((termEquiv p k γ hp hk hreg r hJ n.len).toRingEquiv.toCommRingCatIso) (by
    apply CommRingCat.hom_ext
    exact RingHom.ext (termEquiv p k γ hp hk hreg r hJ n.len).commutes)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- 主完備化の各項と Under の構造射を展開して、環射の合成を照合するため。
private theorem termIso_natural {m n : SimplexCategory} (θ : m ⟶ n) :
    (E).map θ ≫ (termIso p k γ hp hk hreg r hJ n).hom =
      (termIso p k γ hp hk hreg r hJ m).hom ≫ (N).map θ := by
  let f : pdTerm p k r m.len →+* (FrameTerm n.len).carrier :=
    (termEquiv p k γ hp hk hreg r hJ n.len).toRingHom.comp ((E).map θ).right.hom
  let g : pdTerm p k r m.len →+* (FrameTerm n.len).carrier :=
    ((N).map θ).right.hom.comp (termEquiv p k γ hp hk hreg r hJ m.len).toRingHom
  let u := principalCompletionUnitRingHom (Raw m.len) (p : Raw m.len)
  let a : Raw m.len →+* (FrameTerm n.len).carrier :=
    (rawToFrame p k γ hp hk hreg r hJ n.len).toRingHom.comp (pdRawMap k r θ).toRingHom
  have hf : f.comp u = a := by
    apply RingHom.ext
    intro x
    change termEquiv p k γ hp hk hreg r hJ n.len (((E).map θ).right.hom (u x)) = _
    have hn := ringCatMap_comp_unit p ((pdRawModel k r).map θ).right
    rw [show ((E).map θ).right.hom (u x) =
      principalCompletionUnitRingHom (Raw n.len) (p : Raw n.len)
        (((pdRawModel k r).map θ).right.hom x)
      from congrArg (fun f : CommRingCat.of (Raw m.len) ⟶ pdTerm p k r n.len => f x) hn]
    exact termEquiv_unit p k γ hp hk hreg r hJ n.len _
  have hg : g.comp u = a := by
    apply RingHom.ext
    intro x
    change ((N).map θ).right.hom (termEquiv p k γ hp hk hreg r hJ m.len (u x)) = _
    rw [termEquiv_unit]
    exact DFunLike.congr_fun (rawToFrame_natural p k γ hp hk hreg r hJ θ).symm x
  have hc := complete_of_ringHom (R := Raw m.len) (T := (FrameTerm n.len).carrier) p a
    (FrameTerm n.len).isEnvelope.complete
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  change f = g
  exact (principalCompletion_existsUnique_ringHom (Raw m.len) (p : Raw m.len) _ a hc).unique hf hg

end PDSmallModelComparison

/-- 小さい完備分冪模型は、有限個の変数を選んだ枠の分冪 Čech 脈体に同型。 -/
def pdModel_iso_pdCechNerve (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k]
    {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J)
    (_hγ : ∀ n : ℕ, (n.factorial : k) * γ.dpow n (p : k) = (p : k)^n)
    (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
    (hreg : Function.Injective (fun x : k => (p : k) * x)) (r : ℕ)
    (hJ : J ≤ RingHom.ker (algebraMap k (MvPolynomial (Fin r) (k ⧸ J)))) :
    pdModel p k r ≅ pdCechNerve p γ hp hJ
      (fun j : ULift.{u} (Fin r) => (MvPolynomial.X j.down : MvPolynomial (Fin r) (k ⧸ J))) :=
  NatIso.ofComponents (PDSmallModelComparison.termIso p k γ hp hk hreg r hJ)
    (PDSmallModelComparison.termIso_natural p k γ hp hk hreg r hJ)

end SerrePositivity.BhattScholze.Prismatic
