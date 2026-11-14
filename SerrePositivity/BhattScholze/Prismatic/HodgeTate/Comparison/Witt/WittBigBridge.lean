module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigCrystalline
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.BigCechAffineEnvelope
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDPrismMaps
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigCrystalline
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDEnvelopeCrystalline
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.BigPDModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.BigCechAffineEnvelope

/-!
# 大きい Čech–Alexander 模型の結晶の橋

## 概要
大きい prismatic 枠から Witt 係数の分冪 Čech 脈体へ、Frobenius で送る。

## 方針
Frobenius をかける前の多項式評価は評価核を分冪イデアルへ送る。
Frobenius をかけるとその像は (p) に入るので、prismatic envelope の普遍性を適用する。

## 規約
係数の写像は `psiPrism`。枠の各変数はその p 乗へ送る。

## 使われ方
BS 著者版 Theorem 6.4 の結晶の橋。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic.WittBigBridge

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

local notation "C" => (A ⧸ P.ideal)
local notation "W" => WittVector p C

local instance : Algebra W C := (wZero p C).toAlgebra

variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable (Q : Poly (A ⧸ P.ideal)) (n : ℕ)

local notation "γ" => wittPdStructure p C hpC hlocal
local notation "hpW" => p_mem_wittPdIdeal p C
local notation "ker" => WittBigCrystalline.baseKer P
private abbrev largeFrame (Q : Poly C) : polyCompletion P Q.n → bigResidue P Q :=
  Ideal.Quotient.mk (Ideal.span {(p : polyCompletion P Q.n)})

local notation "frame" => largeFrame P

private abbrev termAt (Q : Poly C) (n : ℕ) :
    CompletedPDEnvelopeData p γ (RingHom.ker (pdFrameEval (k := W) (frame Q) n)) :=
  PDCechNerve.term p γ hpW (ker Q) (frame Q) n

private theorem regularAt (Q : Poly C) (n : ℕ) :
    Function.Injective (fun x : (termAt P hpC hlocal Q n).carrier =>
      (p : (termAt P hpC hlocal Q n).carrier) * x) :=
  WittBigCrystalline.regular P hpC hlocal Q n

local notation "Wterm" => termAt P hpC hlocal
local notation "regular" => regularAt P hpC hlocal

private abbrev prismAt (Q : Poly C) (n : ℕ) : OrientedPrism p (Wterm Q n).carrier :=
  wittPDEnvelopeCrystalline hpC hlocal (Wterm Q n) (regular Q n)

local notation "Wprism" => prismAt P hpC hlocal
local notation "E" => Wterm Q n
local notation "T" => Wprism Q n
local notation "S" => BigCechIndex P Q n

private def targetBase : OrientedPrism.Hom P T :=
  (wittPDEnvelopeCrystallineBase hpC hlocal E (regular Q n)).comp
    (psiPrism P hpA hpC)

private def prePsi : A →+* W :=
  (WittVector.map (Ideal.Quotient.mk P.ideal)).comp (deltaWittGhostRingHom P.deltaStructure
    (witt_ghostMap_injective_of_mul_prime_injective p A hpA))

omit [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)] in
private theorem wZero_prePsi (a : A) :
    wZero p C (prePsi P hpA a) = Ideal.Quotient.mk P.ideal a := rfl

private def variableImage (s : S) : (E).carrier :=
  (E).unit (MvPolynomial.X s)

private def preEval : MvPolynomial S A →+* (E).carrier :=
  MvPolynomial.eval₂Hom ((algebraMap W (E).carrier).comp (prePsi P hpA))
    (variableImage P hpC hlocal Q n)

private def eval : MvPolynomial S A →+* (E).carrier :=
  (T).deltaStructure.frobeniusLift.comp (preEval P hpA hpC hlocal Q n)

private theorem eval_X (s : S) :
    eval P hpA hpC hlocal Q n (MvPolynomial.X s) =
      variableImage P hpC hlocal Q n s ^ p := by
  change (T).deltaStructure.frobeniusLift (preEval P hpA hpC hlocal Q n (MvPolynomial.X s)) = _
  rw [preEval, MvPolynomial.eval₂Hom_X', DeltaStructure.frobeniusLift_apply, variableImage]
  have h : (T).deltaStructure.delta ((E).unit (MvPolynomial.X s)) = 0 :=
    wittPDEnvelopeCrystalline_delta_X hpC hlocal E (regular Q n) s
  rw [h, mul_zero, add_zero]

private theorem eval_C (a : A) :
    eval P hpA hpC hlocal Q n (MvPolynomial.C a) =
      (targetBase P hpA hpC hlocal Q n).toRingHom a := by
  let b := wittPDEnvelopeCrystallineBase hpC hlocal E (regular Q n)
  change (T).deltaStructure.frobeniusLift (preEval P hpA hpC hlocal Q n (MvPolynomial.C a)) = _
  rw [preEval, MvPolynomial.eval₂Hom_C]
  change (T).deltaStructure.frobeniusLift (b.toRingHom (prePsi P hpA a)) =
    b.toRingHom (psiRing P hpA a)
  exact (b.map_delta.map_frobeniusLift (prePsi P hpA a)).symm.trans
    (congrArg b.toRingHom (by
      change (wittCrystallineDelta hpC).frobeniusLift (prePsi P hpA a) = psiRing P hpA a
      rw [wittCrystallineDelta_frobenius]
      rfl))

omit [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)] in
private theorem preEval_kernel :
    (RingHom.ker (bigCechEval Q n)).map (preEval P hpA hpC hlocal Q n) ≤ (E).ideal := by
  let e := PDCechNerve.augmentation p γ hpW (ker Q) (frame Q) n
  have h : e.toRingHom.comp (preEval P hpA hpC hlocal Q n) =
      (Ideal.Quotient.mk (Ideal.span {(p : polyCompletion P Q.n)})).comp (bigCechEval Q n) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change e (preEval P hpA hpC hlocal Q n (MvPolynomial.C a)) =
        Ideal.Quotient.mk _ (bigCechEval Q n (MvPolynomial.C a))
      rw [preEval, MvPolynomial.eval₂Hom_C]
      let D := PDCechNerve.term p γ hpW (ker Q) (frame Q) n
      change e (algebraMap W D.carrier (prePsi P hpA a)) = _
      rw [e.commutes]
      change Ideal.Quotient.mk _ (algebraMap C _ (wZero p C (prePsi P hpA a))) = _
      rw [wZero_prePsi, bigCechEval, MvPolynomial.eval₂Hom_C]
      rfl
    · intro s
      change e (preEval P hpA hpC hlocal Q n (MvPolynomial.X s)) =
        Ideal.Quotient.mk _ (bigCechEval Q n (MvPolynomial.X s))
      rw [preEval, MvPolynomial.eval₂Hom_X', bigCechEval, MvPolynomial.eval₂Hom_X']
      exact PDCechNerve.augmentation_variableImage p γ hpW (ker Q) (frame Q) n s
  have he : RingHom.ker e.toRingHom = (E).ideal :=
    PDCechNerve.augmentation_ker p γ hpW (ker Q) (frame Q) n
  rw [Ideal.map_le_iff_le_comap, ← he]
  intro x hx
  change (e.toRingHom.comp (preEval P hpA hpC hlocal Q n)) x = 0
  rw [h, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]

private theorem eval_kernel :
    (RingHom.ker (bigCechEval Q n)).map (eval P hpA hpC hlocal Q n) ≤ (T).ideal := by
  unfold eval
  rw [← Ideal.map_map]
  have h := wittPDEnvelopeCrystalline_frobenius_isDPMorphism hpC hlocal E
    (regular Q n)
  change _ ≤ Ideal.span {(T).generator}
  have hg : (T).generator = p :=
    wittPDEnvelopeCrystalline_generator hpC hlocal E (regular Q n)
  rw [hg]
  exact (Ideal.map_mono (preEval_kernel P hpA hpC hlocal Q n)).trans h.ideal_comp

private theorem existsUnique_free :
    ∃! g : completedFreeDelta P S →+* (E).carrier,
      (completedFreeDeltaStructure P S).IsDeltaHom (T).deltaStructure g ∧
      g.comp (completedFreeDeltaBase P S) = (targetBase P hpA hpC hlocal Q n).toRingHom ∧
      ∀ s, g (completedFreeDeltaVariable P S s) = variableImage P hpC hlocal Q n s ^ p :=
  existsUnique_completedFreeDeltaHom P S (T).deltaStructure
    (targetBase P hpA hpC hlocal Q n).toRingHom (targetBase P hpA hpC hlocal Q n).map_delta
    (T).complete_p (targetBase P hpA hpC hlocal Q n).isModuleComplete_map_generator
    (fun s => variableImage P hpC hlocal Q n s ^ p)

private def freeMap : completedFreeDelta P S →+* (E).carrier :=
  (existsUnique_free P hpA hpC hlocal Q n).choose

private theorem freeMap_spec :
    (completedFreeDeltaStructure P S).IsDeltaHom (T).deltaStructure
        (freeMap P hpA hpC hlocal Q n) ∧
      (freeMap P hpA hpC hlocal Q n).comp (completedFreeDeltaBase P S) =
        (targetBase P hpA hpC hlocal Q n).toRingHom ∧
      ∀ s, freeMap P hpA hpC hlocal Q n (completedFreeDeltaVariable P S s) =
        variableImage P hpC hlocal Q n s ^ p :=
  (existsUnique_free P hpA hpC hlocal Q n).choose_spec.1

private theorem freeMap_initial :
    (freeMap P hpA hpC hlocal Q n).comp (bigCechInitial P Q n) = eval P hpA hpC hlocal Q n := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change freeMap P hpA hpC hlocal Q n (bigCechInitial P Q n (MvPolynomial.C a)) = _
    rw [bigCechInitial_C, eval_C]
    exact RingHom.congr_fun (freeMap_spec P hpA hpC hlocal Q n).2.1 a
  · intro s
    change freeMap P hpA hpC hlocal Q n (bigCechInitial P Q n (MvPolynomial.X s)) = _
    rw [bigCechInitial_X, eval_X]
    exact (freeMap_spec P hpA hpC hlocal Q n).2.2 s

variable (X : BigCechTerm P Q n)

private theorem existsUnique_bridge :
    ∃! g : X.carrier →+* (E).carrier, X.prism.deltaStructure.IsDeltaHom (T).deltaStructure g ∧
      g.comp X.unit = freeMap P hpA hpC hlocal Q n := by
  refine X.isEnvelope.lift T _ (freeMap_spec P hpA hpC hlocal Q n).1 ?_ ?_
  · rw [(freeMap_spec P hpA hpC hlocal Q n).2.1]
    exact (targetBase P hpA hpC hlocal Q n).ideal_le
  · rw [bigCechIdeal, Ideal.map_map, freeMap_initial]
    exact eval_kernel P hpA hpC hlocal Q n

/-- 結晶の橋の各次数での環射。 -/
private def bridgeAt : X.carrier →+* (E).carrier :=
  (existsUnique_bridge P hpA hpC hlocal Q n X).choose

private theorem bridgeAt_spec :
    X.prism.deltaStructure.IsDeltaHom (T).deltaStructure (bridgeAt P hpA hpC hlocal Q n X) ∧
      (bridgeAt P hpA hpC hlocal Q n X).comp X.base.toRingHom =
        (targetBase P hpA hpC hlocal Q n).toRingHom ∧
      ∀ s, bridgeAt P hpA hpC hlocal Q n X (X.variableImage s) =
        variableImage P hpC hlocal Q n s ^ p := by
  have h := (existsUnique_bridge P hpA hpC hlocal Q n X).choose_spec.1
  have hcomp : (bridgeAt P hpA hpC hlocal Q n X).comp X.unit = freeMap P hpA hpC hlocal Q n := h.2
  refine ⟨h.1, ?_, ?_⟩
  · change (bridgeAt P hpA hpC hlocal Q n X).comp (X.unit.comp _) = _
    rw [← RingHom.comp_assoc, hcomp]
    exact (freeMap_spec P hpA hpC hlocal Q n).2.1
  · intro s
    change ((bridgeAt P hpA hpC hlocal Q n X).comp X.unit) (completedFreeDeltaVariable P S s) = _
    rw [hcomp]
    exact (freeMap_spec P hpA hpC hlocal Q n).2.2 s

omit [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)] in
private theorem hom_ext {R : Type u} [CommRing R] (U : OrientedPrism p R)
    (b : OrientedPrism.Hom P U) {f g : X.carrier →+* R}
    (hf : X.prism.deltaStructure.IsDeltaHom U.deltaStructure f)
    (hg : X.prism.deltaStructure.IsDeltaHom U.deltaStructure g)
    (hfB : f.comp X.base.toRingHom = b.toRingHom)
    (hgB : g.comp X.base.toRingHom = b.toRingHom)
    (hv : ∀ s, f (X.variableImage s) = g (X.variableImage s)) : f = g := by
  have hb : (g.comp X.unit).comp (completedFreeDeltaBase P S) = b.toRingHom := by
    rwa [RingHom.comp_assoc]
  have hi : (bigCechIdeal P Q n).map (g.comp X.unit) ≤ U.ideal := by
    rw [← Ideal.map_map]
    apply (Ideal.map_mono X.isEnvelope.map_le).trans
    rw [X.isEnvelope.ideal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    change ((g.comp X.unit).comp (completedFreeDeltaBase P S)) P.generator ∈ U.ideal
    rw [hb]
    exact b.ideal_le (show P.generator ∈ P.ideal from Ideal.subset_span (Set.mem_singleton _))
  have heq : f.comp X.unit = g.comp X.unit := by
    apply completedFreeDeltaHom_ext P S U.deltaStructure b.toRingHom b.map_delta
      U.complete_p b.isModuleComplete_map_generator
      (hf.comp X.isEnvelope.isDeltaHom) (hg.comp X.isEnvelope.isDeltaHom)
    · rwa [RingHom.comp_assoc]
    · exact hb
    · exact hv
  have h := X.isEnvelope.lift U (g.comp X.unit) (hg.comp X.isEnvelope.isDeltaHom)
    (by rw [hb]; exact b.ideal_le) hi
  exact h.unique ⟨hf, heq⟩ ⟨hg, rfl⟩

section Maps

open PDCechNerve

variable {Q₁ Q₂ : Poly (A ⧸ P.ideal)} {m₁ m₂ : ℕ}
variable (f : Q₁ ⟶ Q₂) (θ : Fin (m₁ + 1) → Fin (m₂ + 1))

local notation "E₁" => Wterm Q₁ m₁
local notation "E₂" => Wterm Q₂ m₂
local notation "T₁" => Wprism Q₁ m₁
local notation "T₂" => Wprism Q₂ m₂
local notation "rmap" => bigResidueMap (k := W) P f

private def targetMap : (E₁).carrier →ₐ[W] (E₂).carrier := by
  exact (mapCopies p γ hpW (ker Q₂) (frame Q₂) (m := m₁) (n := m₂) θ).comp
    (renameAt p γ hpW (ker Q₁) (ker Q₂) (frame Q₁) (frame Q₂)
      rmap (polyCompletionMap P f) (fun x => (bigResidueMap_mk P f x).symm) m₁)

omit [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)] in
private theorem targetMap_variable (s : BigCechIndex P Q₁ m₁) :
    targetMap P hpC hlocal f θ (variableImage P hpC hlocal Q₁ m₁ s) =
      variableImage P hpC hlocal Q₂ m₂ (BigCechTerm.indexMap f θ s) := by
  change mapCopies p γ hpW (ker Q₂) (frame Q₂) (m := m₁) (n := m₂) θ
    (renameAt p γ hpW (ker Q₁) (ker Q₂) (frame Q₁) (frame Q₂) rmap
      (polyCompletionMap P f) (fun x => (bigResidueMap_mk P f x).symm) m₁
      (PDCechNerve.variableImage p γ hpW (ker Q₁) (frame Q₁) m₁ s)) =
    PDCechNerve.variableImage p γ hpW (ker Q₂) (frame Q₂) m₂ (BigCechTerm.indexMap f θ s)
  rw [renameAt_variableImage, mapCopies_variableImage]
  rfl

private theorem targetMap_delta :
    (T₁).deltaStructure.IsDeltaHom (T₂).deltaStructure (targetMap P hpC hlocal f θ).toRingHom := by
  refine wittPDEnvelopeCrystalline_isDeltaHom hpC hlocal E₁ E₂
    (regular Q₁ m₁) (regular Q₂ m₂) (targetMap P hpC hlocal f θ) ?_
    (BigCechTerm.indexMap f θ) (targetMap_variable P hpC hlocal f θ)
  exact (mapCopies_isDPMorphism p γ hpW (ker Q₂) (frame Q₂) θ).comp _
    (renameAt_isDPMorphism p γ hpW (ker Q₁) (ker Q₂) (frame Q₁) (frame Q₂)
      rmap (polyCompletionMap P f) (fun x => (bigResidueMap_mk P f x).symm) m₁)

private theorem targetMap_base :
    (targetMap P hpC hlocal f θ).toRingHom.comp (targetBase P hpA hpC hlocal Q₁ m₁).toRingHom =
      (targetBase P hpA hpC hlocal Q₂ m₂).toRingHom := by
  apply RingHom.ext
  intro x
  change targetMap P hpC hlocal f θ (algebraMap W (E₁).carrier (psiRing P hpA x)) =
    algebraMap W (E₂).carrier (psiRing P hpA x)
  exact (targetMap P hpC hlocal f θ).commutes _

private theorem naturality (X₁ : BigCechTerm P Q₁ m₁) (X₂ : BigCechTerm P Q₂ m₂) :
    (bridgeAt P hpA hpC hlocal Q₂ m₂ X₂).comp (X₁.map X₂ f θ) =
      (targetMap P hpC hlocal f θ).toRingHom.comp (bridgeAt P hpA hpC hlocal Q₁ m₁ X₁) := by
  have h₁ := bridgeAt_spec P hpA hpC hlocal Q₁ m₁ X₁
  have h₂ := bridgeAt_spec P hpA hpC hlocal Q₂ m₂ X₂
  apply hom_ext P Q₁ m₁ X₁ T₂ (targetBase P hpA hpC hlocal Q₂ m₂)
    (h₂.1.comp (X₁.map_isDeltaHom X₂ f θ)) ((targetMap_delta P hpC hlocal f θ).comp h₁.1)
  · rw [RingHom.comp_assoc, X₁.map_base, h₂.2.1]
  · rw [RingHom.comp_assoc, h₁.2.1, targetMap_base]
  · intro s
    rw [RingHom.comp_apply, RingHom.comp_apply, X₁.map_variableImage,
      h₂.2.2 (BigCechTerm.indexMap f θ s), h₁.2.2 s, map_pow]
    exact congrArg (fun z => z ^ p) (targetMap_variable P hpC hlocal f θ s).symm

end Maps

omit [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)] in
private theorem targetMap_id_poly {m₁ m₂ : ℕ} (θ : Fin (m₁ + 1) → Fin (m₂ + 1)) :
    targetMap P hpC hlocal (𝟙 Q) θ =
      PDCechNerve.mapCopies p (wittPdStructure p C hpC hlocal) (p_mem_wittPdIdeal p C)
        (WittBigCrystalline.baseKer P Q) (Ideal.Quotient.mk _) θ := by
  unfold targetMap
  let h (x : polyCompletion P Q.n) := (bigResidueMap_mk (k := W) P (𝟙 Q) x).symm
  have hi : PDCechNerve.renameAt p γ hpW (ker Q) (ker Q) (frame Q) (frame Q)
      (bigResidueMap (k := W) P (𝟙 Q)) (polyCompletionMap P (𝟙 Q)) h m₁ =
        AlgHom.id W (Wterm Q m₁).carrier := by
    apply PDCechNerve.hom_ext p γ hpW (ker Q) (frame Q) (Wterm Q m₁).isEnvelope.complete
      (PDCechNerve.renameAt_isDPMorphism p γ hpW (ker Q) (ker Q) (frame Q) (frame Q)
        (bigResidueMap (k := W) P (𝟙 Q)) (polyCompletionMap P (𝟙 Q)) h m₁)
      (DividedPowers.DPMorphism.id (Wterm Q m₁).dividedPowers).isDPMorphism
    intro x
    simp only [PDCechNerve.renameAt_variableImage, polyCompletionMap_id, AlgHom.id_apply]
  rw [hi, AlgHom.comp_id]

omit [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)] in
private theorem targetMap_id_simplex {Q₁ Q₂ : Poly (A ⧸ P.ideal)} (f : Q₁ ⟶ Q₂) (n : ℕ) :
    targetMap P hpC hlocal f (id : Fin (n + 1) → _) =
      PDCechNerve.renameAt p (wittPdStructure p C hpC hlocal) (p_mem_wittPdIdeal p C)
        (WittBigCrystalline.baseKer P Q₁) (WittBigCrystalline.baseKer P Q₂)
        (Ideal.Quotient.mk _) (Ideal.Quotient.mk _) (bigResidueMap (k := W) P f)
        (polyCompletionMap P f) (fun x => (bigResidueMap_mk P f x).symm) n := by
  unfold targetMap
  rw [PDCechNerve.mapCopies_id, AlgHom.id_comp]

local notation "resA" => Under.map (CommRingCat.ofHom (psiRing P hpA))
local notation "resCosimplicial" => Functor.obj (Functor.whiskeringRight SimplexCategory _ _) resA

private def bridgeOnTerms (X : ∀ (Q : Poly C) n, BigCechTerm P Q n) :
    bigCechAlexanderOfTerms P X ⟶ wittBigPdModel P hpC hlocal ⋙ resCosimplicial where
  app Q := {
    app n := Under.homMk (CommRingCat.ofHom (bridgeAt P hpA hpC hlocal Q n.len (X Q n.len)))
      (CommRingCat.hom_ext (bridgeAt_spec P hpA hpC hlocal Q n.len (X Q n.len)).2.1)
    naturality {m n} θ := by
      apply Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      have h := naturality P hpA hpC hlocal (𝟙 Q) θ.toOrderHom (X Q m.len) (X Q n.len)
      rw [targetMap_id_poly] at h
      exact h }
  naturality {Q₁ Q₂} f := by
    apply NatTrans.ext
    funext n
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    have h := naturality P hpA hpC hlocal f (id : Fin (n.len + 1) → _) (X Q₁ n.len) (X Q₂ n.len)
    rw [targetMap_id_simplex] at h
    exact h

/-- 有界 prism 上の大きい Čech–Alexander 模型からの厳密な結晶の橋。 -/
def _root_.SerrePositivity.BhattScholze.Prismatic.wittBigBridge (hP : IsBoundedPrism P) :
    bigCechAlexander P hP ⟶ wittBigPdModel P hpC hlocal ⋙ resCosimplicial :=
  bridgeOnTerms P hpA hpC hlocal (fun Q n => affineBigCechTerm P Q n hP)

end SerrePositivity.BhattScholze.Prismatic.WittBigBridge
