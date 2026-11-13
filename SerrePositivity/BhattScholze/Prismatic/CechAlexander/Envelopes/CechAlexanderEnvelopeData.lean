module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderPresentation
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDelta
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.Envelope

/-!
# 一般の剰余環に対する Čech–Alexander 包絡のデータ

## 概要
原典の導来閉包のイデアルと HasEnvelopes を定め、選んだ包絡の剰余構造射を作る。

## 方針
評価核の生成イデアルと導来閉包の包絡の同値を使う。評価は各元を一つの変数の像として全射。

## 規約
BS 著者版 Construction 4.17–4.18。一般の包絡の存在をここでは仮定する。

## 使われ方
HasEnvelopes からの site の余単体的対象の組み立て。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open CategoryTheory SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]

/-- 各元と頂点を添字とする変数。BS 著者版 Construction 4.18。 -/
abbrev cechIndex (n : ℕ) : Type u := R × Fin (n + 1)

/-- 完備自由 δ 環。BS 著者版 Construction 4.17 の B。 -/
abbrev cechFreeDelta (n : ℕ) : Type u := completedFreeDelta P (cechIndex R n)

/-- 各変数をその添字の元へ評価する環射。 -/
@[expose] def cechEval (n : ℕ) : MvPolynomial (cechIndex R n) A →+* R :=
  MvPolynomial.eval₂Hom
    ((algebraMap (A ⧸ P.ideal) R).comp (Ideal.Quotient.mk P.ideal)) Prod.fst

/-- 評価の始域の多項式環から完備自由 δ 環への標準射。 -/
@[expose] def cechInitial (n : ℕ) : MvPolynomial (cechIndex R n) A →+* cechFreeDelta P R n :=
  (pdCompletionUnit _ p (algebraMap A _ P.generator)).comp
    (relativeFreeInitialPolynomialMap (cechIndex R n) A).toRingHom

@[simp] theorem cechInitial_X (n : ℕ) (s : cechIndex R n) :
    cechInitial P R n (MvPolynomial.X s) = completedFreeDeltaVariable P _ s := by
  change pdCompletionUnit _ p _ (relativeFreeInitialPolynomialMap _ _ (MvPolynomial.X s)) = _
  rw [relativeFreeInitialPolynomialMap, MvPolynomial.rename_X]
  rfl

@[simp] theorem cechInitial_C (n : ℕ) (a : A) :
    cechInitial P R n (MvPolynomial.C a) = completedFreeDeltaBase P _ a := by
  change pdCompletionUnit _ p _ (relativeFreeInitialPolynomialMap _ _ (MvPolynomial.C a)) = _
  rw [relativeFreeInitialPolynomialMap, MvPolynomial.rename_C]
  rfl

/-- 評価核の生成イデアル。閉包との比較のための補助イデアル。 -/
@[expose] def cechRawKernel (n : ℕ) : Ideal (cechFreeDelta P R n) :=
  (RingHom.ker (cechEval P R n)).map (cechInitial P R n)

/-- 概要：原典の J は通常商の導来 p 完備化の H⁰ への射の核。
方針：既存の envelopeClosure を評価核の生成イデアルへ適用する。
規約：BS 著者版 Construction 4.17。通常の p 進閉包へ置き換えない。
使われ方：HasEnvelopes のイデアル。 -/
@[expose] def cechKernel (n : ℕ) : Ideal (cechFreeDelta P R n) :=
  envelopeClosure p (cechRawKernel P R n)

theorem generator_mem_cechRawKernel (n : ℕ) :
    completedFreeDeltaBase P _ P.generator ∈ cechRawKernel P R n := by
  rw [← cechInitial_C P R n]
  apply Ideal.mem_map_of_mem
  change cechEval P R n (MvPolynomial.C P.generator) = 0
  rw [cechEval, MvPolynomial.eval₂Hom_C]
  change algebraMap (A ⧸ P.ideal) R (Ideal.Quotient.mk P.ideal P.generator) = 0
  have hz : Ideal.Quotient.mk P.ideal P.generator = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hz, map_zero]

/-- 基底の生成元は原典の閉包イデアルに入る。 -/
theorem generator_mem_cechKernel (n : ℕ) :
    completedFreeDeltaBase P _ P.generator ∈ cechKernel P R n :=
  le_envelopeClosure p _ (generator_mem_cechRawKernel P R n)

/-- 概要：各項の原典の包絡が存在し、有界かつ指定された cutoff に収まるという仮定。
方針：drafts の HasEnvelopes の存在命題をそのまま使う。
規約：BS 著者版 Construction 4.18、D21。一般の存在を主張しない。
使われ方：包絡を選択して site の対象を作る。 -/
@[expose] def HasEnvelopes : Prop :=
  ∀ n : ℕ, ∃ (C : Type u) (rc : CommRing C),
    letI := rc
    ∃ (Q : OrientedPrism p C) (η : cechFreeDelta P R n →+* C),
      IsPrismaticEnvelope P (completedFreeDeltaStructure P _) (completedFreeDeltaBase P _)
        (completedFreeDeltaBase_isDeltaHom P _) (cechKernel P R n)
        (generator_mem_cechKernel P R n) Q η ∧
      IsBoundedPrism Q ∧ Cardinal.mk C ≤ cutoff A R

/-- 選択した包絡の計算用データ。生の核に関する普遍性は閉包の比較から得る。 -/
structure CechEnvelopeTerm (n : ℕ) where
  carrier : Type u
  [ring : CommRing carrier]
  prism : OrientedPrism p carrier
  unit : cechFreeDelta P R n →+* carrier
  isEnvelope : IsPrismaticEnvelope P (completedFreeDeltaStructure P _)
    (completedFreeDeltaBase P _) (completedFreeDeltaBase_isDeltaHom P _)
    (cechRawKernel P R n) (generator_mem_cechRawKernel P R n) prism unit
  bounded : IsBoundedPrism prism
  small : Cardinal.mk carrier ≤ cutoff A R
attribute [instance] CechEnvelopeTerm.ring

/-- 概要：HasEnvelopes から各項の包絡を選ぶ。
方針：原典の閉包の包絡を選び、of_closure によって同じ包の生の核の普遍性を取り出す。
規約：BS 著者版 Construction 4.18。使われ方：以後の一意な射の構成。 -/
def HasEnvelopes.term (h : HasEnvelopes P R) (n : ℕ) : CechEnvelopeTerm P R n := by
  classical
  let C := (h n).choose
  letI : CommRing C := (h n).choose_spec.choose
  let Q := (h n).choose_spec.choose_spec.choose
  let η := (h n).choose_spec.choose_spec.choose_spec.choose
  have hw := (h n).choose_spec.choose_spec.choose_spec.choose_spec
  exact ⟨C, Q, η,
    (IsPrismaticEnvelope.of_closure P _ _ _ (cechRawKernel P R n)
      (generator_mem_cechRawKernel P R n) Q η).mpr hw.1, hw.2.1, hw.2.2⟩

namespace CechEnvelopeTerm
variable {P R} {n : ℕ} (E : CechEnvelopeTerm P R n)

/-- 包の基底 prism 射。 -/
@[expose] def base : OrientedPrism.Hom P E.prism :=
  ⟨E.unit.comp (completedFreeDeltaBase P _),
    E.isEnvelope.isDeltaHom.comp (completedFreeDeltaBase_isDeltaHom P _),
    E.isEnvelope.base_hom⟩

/-- 包の初期変数の像。 -/
@[expose] def variableImage (s : cechIndex R n) : E.carrier :=
  E.unit (completedFreeDeltaVariable P _ s)

private theorem eval_surjective : Function.Surjective (cechEval P R n) := by
  intro r
  exact ⟨MvPolynomial.X (r, 0), MvPolynomial.eval₂Hom_X' _ _ _⟩

private def unitMod : MvPolynomial (cechIndex R n) A →+* E.carrier ⧸ E.prism.ideal :=
  (Ideal.Quotient.mk E.prism.ideal).comp (E.unit.comp (cechInitial P R n))

private theorem ker_le_unitMod : RingHom.ker (cechEval P R n) ≤ RingHom.ker E.unitMod := by
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact E.isEnvelope.map_le (Ideal.mem_map_of_mem E.unit (Ideal.mem_map_of_mem _ hx))

/-- 評価の全射を経由して得る剰余環からの標準射。 -/
def residueSection : R →+* E.carrier ⧸ E.prism.ideal :=
  (cechEval P R n).liftOfSurjective (eval_surjective (P := P) (R := R) (n := n)) ⟨E.unitMod, E.ker_le_unitMod⟩

/-- 剰余の標準射は変数の添字の元をその変数の剰余へ送る。 -/
theorem residueSection_variable (s : cechIndex R n) :
    E.residueSection s.1 = Ideal.Quotient.mk E.prism.ideal (E.variableImage s) := by
  have he : E.residueSection.comp (cechEval P R n) = E.unitMod :=
    RingHom.liftOfSurjective_comp _ _ _
  have h := RingHom.congr_fun he (MvPolynomial.X s)
  change E.residueSection (cechEval P R n (MvPolynomial.X s)) =
    Ideal.Quotient.mk E.prism.ideal (E.unit (cechInitial P R n (MvPolynomial.X s))) at h
  rwa [cechEval, MvPolynomial.eval₂Hom_X', cechInitial_X] at h

/-- 剰余の標準射は基底の商の射を延長する。 -/
theorem residueSection_comp :
    E.residueSection.comp (algebraMap (A ⧸ P.ideal) R) = E.base.quotientMap := by
  have he : E.residueSection.comp (cechEval P R n) = E.unitMod :=
    RingHom.liftOfSurjective_comp _ _ _
  apply RingHom.ext
  intro c
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  have h := RingHom.congr_fun he (MvPolynomial.C a)
  change E.residueSection (cechEval P R n (MvPolynomial.C a)) =
    Ideal.Quotient.mk E.prism.ideal (E.unit (cechInitial P R n (MvPolynomial.C a))) at h
  rw [cechEval, MvPolynomial.eval₂Hom_C, cechInitial_C] at h
  exact h

end CechEnvelopeTerm
end SerrePositivity.BhattScholze.Prismatic
