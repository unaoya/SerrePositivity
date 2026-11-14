module

public import SerrePositivity.BhattScholze.Andre.Envelope.DivisionResidue
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Adjoin
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.List.Nodup
public import SerrePositivity.HomologicalAlgebra.DerivedTensor
public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.HomologicalAlgebra.TorFlatBaseChangeVanishing
public import SerrePositivity.HomologicalAlgebra.KoszulTensorConeComparison
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import SerrePositivity.HomologicalAlgebra.KoszulModuleBounds
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic
public import Mathlib.Algebra.CharP.Lemmas

/-!
# 根の関係式の正則性と Koszul 分解（BS 著者版 Proposition 3.13・BS 著者版 Example 3.14 を根の関係式に限った形の土台）

## 概要
根添加の多項式関係による具体的係数商とその自由性・忠実平坦性、根 δ 除算添加環の源変数と raw 剰余、先行する根関係・任意の先行添字集合による商、有限根関係列の弱正則性・Koszul 分解・係数側 Tor、p 乗商での後続根関係の正則性、二つの独立根関係の raw 除算への正則入力。
根関係の正則性と Koszul 分解は、BS 著者版 Proposition 3.13 の包の平坦性を根の入力で扱うための補助である。

## 方針
原典の「正則列の envelope は平坦」（BS 著者版 Proposition 3.13）を、根の関係 fᵢ(Xᵢ)/d の場合に Koszul 複体で直接示す。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/JetKoszul`、`Envelope/JetRegularity`、`Envelope/NormalizedStep`、`Envelope/PDivision`、`Envelope/RootFamilyRaw`、`Envelope/RootResidueKoszul`、`Envelope/RootSource`、`Envelope/SourceEvaluation`、`RootEnvelope/Source`。
-/

universe u v w

/-! ## 根添加の多項式関係による具体的係数商 -/

@[expose] public noncomputable section DeltaRootRelationCoefficientQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 既存rank-one多項式δ環に置く、指定元族のp乗根の関係式。 -/
def deltaRootRelationFamily (b : σ → A) (s : σ) : MvPolynomial σ A :=
  MvPolynomial.X s ^ p - MvPolynomial.C (b s)

/-- 根関係族について既存除算包の係数商A[X_s]/(p,Cd,X_s^p-Cb_s)を使う。 -/
abbrev DeltaRootRelationCoefficientQuotient (d : A) (b : σ → A) :=
  MvPolynomial σ A ⧸
    deltaDivisionFirstBaseIdeal (p := p) (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b)

omit [Fact p.Prime] in
/-- この係数イデアルは、(p,d)の係数拡張と既存モニック根関係イデアルの和。 -/
theorem deltaRootRelationCoefficientIdeal_eq_base_sup (d : A) (b : σ → A) :
    deltaDivisionFirstBaseIdeal (p := p) (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b) =
      Ideal.map MvPolynomial.C (Ideal.span {(p : A), d}) ⊔
        monicPowerFamilyRelationIdeal p σ A b := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast, deltaDivisionFirstBaseIdeal,
    monicPowerFamilyRelationIdeal]
  rfl

/-- 指定根関係の係数商はA/(p,d)上の既存通常モニック根添加環に同型。 -/
def deltaRootRelationCoefficientPowerEquiv (d : A) (b : σ → A) :
    DeltaRootRelationCoefficientQuotient (p := p) d b ≃+*
      MonicPowerFamilyCover p σ (A ⧸ Ideal.span {(p : A), d})
        (fun s => Ideal.Quotient.mk _ (b s)) :=
  (Ideal.quotEquivOfEq (deltaRootRelationCoefficientIdeal_eq_base_sup d b)).trans
    (monicPowerFamilyBaseQuotientEquiv p σ A (Ideal.span {(p : A), d}) b)

omit [Fact p.Prime] in
/-- 根関係の係数商比較は基底係数の標準像に両立する。 -/
theorem deltaRootRelationCoefficientPowerEquiv_C (d : A) (b : σ → A) (c : A) :
    deltaRootRelationCoefficientPowerEquiv (p := p) d b
      (Ideal.Quotient.mk _ (MvPolynomial.C c)) =
      algebraMap (A ⧸ Ideal.span {(p : A), d})
        (MonicPowerFamilyCover p σ (A ⧸ Ideal.span {(p : A), d})
          (fun s => Ideal.Quotient.mk _ (b s))) (Ideal.Quotient.mk _ c) := by
  rw [deltaRootRelationCoefficientPowerEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, monicPowerFamilyBaseQuotientEquiv_C]

omit [Fact p.Prime] in
/-- 根関係の係数商比較は各多項式変数を指定p乗根に送る。 -/
theorem deltaRootRelationCoefficientPowerEquiv_X (d : A) (b : σ → A) (s : σ) :
    deltaRootRelationCoefficientPowerEquiv (p := p) d b
      (Ideal.Quotient.mk _ (MvPolynomial.X s)) =
      monicPowerFamilyRoot p σ (A ⧸ Ideal.span {(p : A), d})
        (fun t => Ideal.Quotient.mk _ (b t)) s := by
  rw [deltaRootRelationCoefficientPowerEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, monicPowerFamilyBaseQuotientEquiv_X]

end SerrePositivity.BhattScholze

end DeltaRootRelationCoefficientQuotient

/-! ## 根関係の正則性とKoszul分解

係数環のp正則性・非零性・Noether性を仮定しない。
相対完全正則性や完備化後の平坦性とは区別する。
-/

@[expose] public noncomputable section DeltaRootRelationKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 任意の指定変数の根関係は、係数環に依らず非零因子。 -/
theorem deltaRootRelation_isSMulRegular (b : σ → A) (s : σ) :
    IsSMulRegular (MvPolynomial σ A) (deltaRootRelationFamily (p := p) b s) :=
  monicPowerFamilyRelation_isSMulRegular (Fact.out : p.Prime).ne_zero b s

/-- 一つの根関係の列は弱正則。零環も許す。 -/
theorem deltaRootRelation_singleton_isWeaklyRegular (b : σ → A) (s : σ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      [deltaRootRelationFamily (p := p) b s] :=
  (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr
    (deltaRootRelation_isSMulRegular b s)

/-- 一つの根関係のKoszul複体は、実際の通常商の自由分解。 -/
theorem deltaRootRelation_singleton_isKoszulResolution (b : σ → A) (s : σ) :
    SerrePositivity.IsKoszulResolution
      (fun _ : Fin 1 ↦ deltaRootRelationFamily (p := p) b s) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa using deltaRootRelation_singleton_isWeaklyRegular (p := p) b s

/-- 任意係数変更後でも、一つの根関係の標準像は非零因子。 -/
theorem deltaRootRelation_map_isSMulRegular {B : Type w} [CommRing B]
    (f : A →+* B) (b : σ → A) (s : σ) :
    IsSMulRegular (MvPolynomial σ B)
      (MvPolynomial.map f (deltaRootRelationFamily (p := p) b s)) := by
  simpa only [deltaRootRelationFamily, map_sub, map_pow, MvPolynomial.map_X,
    MvPolynomial.map_C] using
    deltaRootRelation_isSMulRegular (p := p) (fun t ↦ f (b t)) s

/-- 任意係数変更後の標準根関係のKoszul複体も通常商の分解となる。 -/
theorem deltaRootRelation_map_singleton_isKoszulResolution {B : Type w} [CommRing B]
    (f : A →+* B) (b : σ → A) (s : σ) :
    SerrePositivity.IsKoszulResolution (fun _ : Fin 1 ↦
      MvPolynomial.map f (deltaRootRelationFamily (p := p) b s)) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [List.ofFn_const, List.replicate_one,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact deltaRootRelation_map_isSMulRegular f b s

end SerrePositivity.BhattScholze

end DeltaRootRelationKoszul

/-! ## 先行する根関係で割った商の具体的な多項式表示

添字を残りの変数τと先行変数ιの直和として表示する。
根添加済み係数環は既存MonicPowerFamilyCoverを使用する。
-/

@[expose] public noncomputable section DeltaRootPartialQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A] {τ : Type v} {ι : Type w}
variable (b : τ ⊕ ι → A)

/-- 先行変数のみの根関係を課すイデアル。 -/
def deltaRootPartialRelationIdeal : Ideal (MvPolynomial (τ ⊕ ι) A) :=
  Ideal.span (Set.range fun s : ι ↦ deltaRootRelationFamily (p := p) b (Sum.inr s))

/-- 添字分割同型は先行根関係を係数側の関係式イデアルへ送る。 -/
theorem deltaRootPartialRelationIdeal_map_sum :
    (deltaRootPartialRelationIdeal (p := p) b).map
      (MvPolynomial.sumRingEquiv A τ ι).toRingHom =
    (monicPowerFamilyRelationIdeal p ι A (fun s ↦ b (Sum.inr s))).map
      (MvPolynomial.C : MvPolynomial ι A →+* MvPolynomial τ (MvPolynomial ι A)) := by
  simp only [deltaRootPartialRelationIdeal, monicPowerFamilyRelationIdeal, Ideal.map_span,
    ← Set.range_comp', deltaRootRelationFamily, map_sub, map_pow,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    MvPolynomial.sumRingEquiv_X_inr, MvPolynomial.sumRingEquiv_C]

/-- 先行関係式の商は、既存根添加環を係数環とする残りの変数の多項式環。 -/
def deltaRootPartialQuotientEquiv :
    (MvPolynomial (τ ⊕ ι) A ⧸ deltaRootPartialRelationIdeal (p := p) b) ≃+*
      MvPolynomial τ (MonicPowerFamilyCover p ι A (fun s ↦ b (Sum.inr s))) :=
  ((Ideal.quotientEquiv _ _ (MvPolynomial.sumRingEquiv A τ ι)
    (deltaRootPartialRelationIdeal_map_sum b).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := τ)
      (monicPowerFamilyRelationIdeal p ι A (fun s ↦ b (Sum.inr s)))).symm.toRingEquiv).trans
    (MvPolynomial.mapEquiv τ
      (monicPowerFamilyPresentationEquiv p ι A (fun s ↦ b (Sum.inr s))))

/-- 商同型の標準商射上の具体的な式。 -/
theorem deltaRootPartialQuotientEquiv_mk (x : MvPolynomial (τ ⊕ ι) A) :
    deltaRootPartialQuotientEquiv (p := p) b (Ideal.Quotient.mk _ x) =
      MvPolynomial.map (monicPowerFamilyQuotientMap p ι A (fun s ↦ b (Sum.inr s)))
        (MvPolynomial.map (Ideal.Quotient.mk _) (MvPolynomial.sumRingEquiv A τ ι x)) := by
  change MvPolynomial.map _
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) _).symm
      (Ideal.Quotient.mk _ (MvPolynomial.sumRingEquiv A τ ι x))) = _
  rw [← monicPowerFamilyCoefficientQuotient_comp]
  rfl

/-- 元の係数は根添加済み係数環の標準係数像へ送られる。 -/
theorem deltaRootPartialQuotientEquiv_C (a : A) :
    deltaRootPartialQuotientEquiv (p := p) b (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      MvPolynomial.C (algebraMap A (MonicPowerFamilyCover p ι A (fun s ↦ b (Sum.inr s))) a) := by
  rw [deltaRootPartialQuotientEquiv_mk, MvPolynomial.sumRingEquiv_C,
    MvPolynomial.map_C, MvPolynomial.map_C]
  exact congrArg MvPolynomial.C (monicPowerFamilyPresentationEquiv_coeff p ι A _ a)

/-- 残りの変数はそのまま多項式変数に対応する。 -/
theorem deltaRootPartialQuotientEquiv_X_inl (s : τ) :
    deltaRootPartialQuotientEquiv (p := p) b (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl s))) =
      MvPolynomial.X s := by
  rw [deltaRootPartialQuotientEquiv_mk, MvPolynomial.sumRingEquiv_X_inl,
    MvPolynomial.map_X, MvPolynomial.map_X]

/-- 先行変数は既存の指定根に対応する。 -/
theorem deltaRootPartialQuotientEquiv_X_inr (s : ι) :
    deltaRootPartialQuotientEquiv (p := p) b (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr s))) =
      MvPolynomial.C (monicPowerFamilyRoot p ι A (fun t ↦ b (Sum.inr t)) s) := by
  rw [deltaRootPartialQuotientEquiv_mk, MvPolynomial.sumRingEquiv_X_inr,
    MvPolynomial.map_C, MvPolynomial.map_C]
  exact congrArg MvPolynomial.C (monicPowerFamilyPresentationEquiv_root p ι A _ s)

/-- 先行する根関係で割った後も、残りの各根関係は非零因子。 -/
theorem deltaRootPartialQuotient_remaining_isSMulRegular [Fact p.Prime] (s : τ) :
    IsSMulRegular (MvPolynomial (τ ⊕ ι) A ⧸ deltaRootPartialRelationIdeal (p := p) b)
      (Ideal.Quotient.mk (deltaRootPartialRelationIdeal (p := p) b)
        (deltaRootRelationFamily (p := p) b (Sum.inl s))) := by
  let e := deltaRootPartialQuotientEquiv (p := p) b
  have he : e (Ideal.Quotient.mk (deltaRootPartialRelationIdeal (p := p) b)
      (deltaRootRelationFamily (p := p) b (Sum.inl s))) =
      deltaRootRelationFamily (p := p)
        (fun t : τ ↦ algebraMap A (MonicPowerFamilyCover p ι A
          (fun r ↦ b (Sum.inr r))) (b (Sum.inl t))) s := by
    simp only [deltaRootRelationFamily, map_sub, map_pow, e,
      deltaRootPartialQuotientEquiv_X_inl, deltaRootPartialQuotientEquiv_C]
  have h := deltaRootRelation_isSMulRegular (p := p)
    (fun t : τ ↦ algebraMap A (MonicPowerFamilyCover p ι A
      (fun r ↦ b (Sum.inr r))) (b (Sum.inl t))) s
  intro x y hxy
  apply e.injective
  apply h
  have hh := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using hh

/-- 先行関係式の商上でも、後続一関係のKoszul複体は実際の商の分解となる。 -/
theorem deltaRootPartialQuotient_remaining_isKoszulResolution [Fact p.Prime] (s : τ) :
    SerrePositivity.IsKoszulResolution (fun _ : Fin 1 ↦
      (Ideal.Quotient.mk (deltaRootPartialRelationIdeal (p := p) b)
        (deltaRootRelationFamily (p := p) b (Sum.inl s)))) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [List.ofFn_const, List.replicate_one,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact deltaRootPartialQuotient_remaining_isSMulRegular b s

end SerrePositivity.BhattScholze

end DeltaRootPartialQuotient

/-! ## 任意の先行添字集合の根関係の商

有限性を要求せず、補集合の変数と先行指定根を具体的に分離する。
-/

@[expose] public noncomputable section DeltaRootSubsetQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A] {σ : Type v}

/-- 任意の先行添字集合Tについて、残りの添字を先に置く標準添字分割。 -/
def deltaRootSubsetIndexEquiv (T : Set σ) : σ ≃ (Tᶜ : Set σ) ⊕ T := by
  classical
  exact (Equiv.Set.sumCompl T).symm.trans (Equiv.sumComm _ _)

/-- 先行添字は分割の右側へ送られる。 -/
theorem deltaRootSubsetIndexEquiv_mem (T : Set σ) (s : T) :
    deltaRootSubsetIndexEquiv T s = Sum.inr s := by
  classical
  simp [deltaRootSubsetIndexEquiv]

/-- 残りの添字は分割の左側へ送られる。 -/
theorem deltaRootSubsetIndexEquiv_notMem (T : Set σ) (s : (Tᶜ : Set σ)) :
    deltaRootSubsetIndexEquiv T s = Sum.inl s := by
  classical
  simp [deltaRootSubsetIndexEquiv]

/-- 指定した部分集合の根関係のみを課すイデアル。 -/
def deltaRootSubsetRelationIdeal (T : Set σ) (b : σ → A) : Ideal (MvPolynomial σ A) :=
  Ideal.span (Set.range fun s : T ↦ deltaRootRelationFamily (p := p) b s)

/-- 再添字付けで部分集合の関係式イデアルが先行変数の関係式イデアルへ移る。 -/
theorem deltaRootSubsetRelationIdeal_map_rename (T : Set σ) (b : σ → A) :
    (deltaRootSubsetRelationIdeal (p := p) T b).map
      (MvPolynomial.renameEquiv A (deltaRootSubsetIndexEquiv T)).toRingHom =
    deltaRootPartialRelationIdeal (p := p)
      (Sum.elim (fun t : (Tᶜ : Set σ) ↦ b t) (fun t : T ↦ b t)) := by
  simp only [deltaRootSubsetRelationIdeal, deltaRootPartialRelationIdeal,
    Ideal.map_span, ← Set.range_comp']
  congr 1
  congr 1
  funext s
  simp [deltaRootRelationFamily, MvPolynomial.renameEquiv,
    deltaRootSubsetIndexEquiv_mem]

/-- 任意部分集合の根関係の商は、既存根添加環上の補集合の多項式環。 -/
def deltaRootSubsetQuotientEquiv (T : Set σ) (b : σ → A) :
    (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b) ≃+*
      MvPolynomial (Tᶜ : Set σ) (MonicPowerFamilyCover p T A (fun s ↦ b s)) :=
  (Ideal.quotientEquiv _ _ (MvPolynomial.renameEquiv A
    (deltaRootSubsetIndexEquiv T)).toRingEquiv
    (deltaRootSubsetRelationIdeal_map_rename T b).symm).trans
    (deltaRootPartialQuotientEquiv (p := p)
      (Sum.elim (fun t : (Tᶜ : Set σ) ↦ b t) (fun t : T ↦ b t)))

/-- 部分集合商の同型は元の係数を標準係数像へ送る。 -/
theorem deltaRootSubsetQuotientEquiv_C (T : Set σ) (b : σ → A) (a : A) :
    deltaRootSubsetQuotientEquiv (p := p) T b (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      MvPolynomial.C (algebraMap A (MonicPowerFamilyCover p T A (fun s ↦ b s)) a) := by
  change deltaRootPartialQuotientEquiv _ (Ideal.Quotient.mk _
    (MvPolynomial.renameEquiv A (deltaRootSubsetIndexEquiv T) (MvPolynomial.C a))) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]
  exact deltaRootPartialQuotientEquiv_C _ a

/-- 補集合の変数は、商表示の残りの多項式変数に一致する。 -/
theorem deltaRootSubsetQuotientEquiv_X_notMem (T : Set σ) (b : σ → A)
    (s : (Tᶜ : Set σ)) :
    deltaRootSubsetQuotientEquiv (p := p) T b (Ideal.Quotient.mk _ (MvPolynomial.X (s : σ))) =
      MvPolynomial.X s := by
  change deltaRootPartialQuotientEquiv _ (Ideal.Quotient.mk _
    (MvPolynomial.renameEquiv A (deltaRootSubsetIndexEquiv T) (MvPolynomial.X (s : σ)))) = _
  simp only [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    deltaRootSubsetIndexEquiv_notMem, deltaRootPartialQuotientEquiv_X_inl]

/-- 先行部分集合の変数は既存の指定根の係数像に一致する。 -/
theorem deltaRootSubsetQuotientEquiv_X_mem (T : Set σ) (b : σ → A) (s : T) :
    deltaRootSubsetQuotientEquiv (p := p) T b (Ideal.Quotient.mk _ (MvPolynomial.X (s : σ))) =
      MvPolynomial.C (monicPowerFamilyRoot p T A (fun t ↦ b t) s) := by
  change deltaRootPartialQuotientEquiv _ (Ideal.Quotient.mk _
    (MvPolynomial.renameEquiv A (deltaRootSubsetIndexEquiv T) (MvPolynomial.X (s : σ)))) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, deltaRootSubsetIndexEquiv_mem]
  exact deltaRootPartialQuotientEquiv_X_inr _ s

/-- 先行部分集合に属さない根関係は、その商において非零因子。 -/
theorem deltaRootSubsetQuotient_remaining_isSMulRegular_of_ne_zero (hp : p ≠ 0)
    (T : Set σ) (b : σ → A) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b)
      (Ideal.Quotient.mk (deltaRootSubsetRelationIdeal (p := p) T b)
        (deltaRootRelationFamily (p := p) b s)) := by
  let e := deltaRootSubsetQuotientEquiv (p := p) T b
  have he : e (Ideal.Quotient.mk (deltaRootSubsetRelationIdeal (p := p) T b)
      (deltaRootRelationFamily (p := p) b s)) =
      deltaRootRelationFamily (p := p)
        (fun t : (Tᶜ : Set σ) ↦ algebraMap A (MonicPowerFamilyCover p T A
          (fun r ↦ b r)) (b t)) ⟨s, hs⟩ := by
    simp only [deltaRootRelationFamily, map_sub, map_pow, e,
      deltaRootSubsetQuotientEquiv_C]
    rw [deltaRootSubsetQuotientEquiv_X_notMem T b ⟨s, hs⟩]
  have h := monicPowerFamilyRelation_isSMulRegular hp
    (fun t : (Tᶜ : Set σ) ↦ algebraMap A (MonicPowerFamilyCover p T A
      (fun r ↦ b r)) (b t)) (⟨s, hs⟩ : (Tᶜ : Set σ))
  intro x y hxy
  apply e.injective
  apply h
  have hh := congrArg e hxy
  simp only [smul_eq_mul, map_mul] at hh
  rw [he] at hh
  simpa only [deltaRootRelationFamily, smul_eq_mul] using hh


/-- 先行部分集合に属さない根関係は、その商において非零因子。 -/
theorem deltaRootSubsetQuotient_remaining_isSMulRegular [Fact p.Prime]
    (T : Set σ) (b : σ → A) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b)
      (Ideal.Quotient.mk (deltaRootSubsetRelationIdeal (p := p) T b)
        (deltaRootRelationFamily (p := p) b s)) :=
  deltaRootSubsetQuotient_remaining_isSMulRegular_of_ne_zero
    (Fact.out : p.Prime).ne_zero T b s hs

end SerrePositivity.BhattScholze

end DeltaRootSubsetQuotient

/-! ## 有限根関係列の弱正則性と実Koszul分解

重複のない添字列を用いる。係数環のp正則性やNoether性は不要。
相対完全正則性・完備化後の完全平坦性は別工程。
-/

@[expose] public noncomputable section DeltaRootFiniteRegularSequence

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A] {σ : Type v}

/-- 有限根関係列の生成イデアルは、その添字集合の根関係イデアル。 -/
theorem deltaRootRelation_ofList_eq_subset (b : σ → A) (l : List σ) :
    Ideal.ofList (l.map (deltaRootRelationFamily (p := p) b)) =
      deltaRootSubsetRelationIdeal (p := p) {s | s ∈ l} b := by
  rw [Ideal.ofList, deltaRootSubsetRelationIdeal]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_range]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.property, rfl⟩

/-- 異なる有限個の根関係は、任意係数環上の弱正則列。 -/
theorem deltaRootRelation_list_isWeaklyRegular_of_ne_zero (hp : p ≠ 0)
    (b : σ → A) (l : List σ) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (l.map (deltaRootRelationFamily (p := p) b)) := by
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  have hs : l[i] ∉ l.take i := by
    intro hm
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.mp hm
    rw [List.getElem_take] at hji
    have he := hl.getElem_inj_iff.mp hji
    have hj' : j < i := lt_of_lt_of_le hj (List.length_take_le _ _)
    omega
  have h := deltaRootSubsetQuotient_remaining_isSMulRegular_of_ne_zero hp
    {s | s ∈ l.take i} b l[i] hs
  have hr : IsSMulRegular
      (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) {s | s ∈ l.take i} b)
      (deltaRootRelationFamily (p := p) b l[i]) :=
    (isSMulRegular_map (Ideal.Quotient.mk _ ) (fun _ ↦ rfl)).mp h
  have hI : (Ideal.ofList ((l.map (deltaRootRelationFamily (p := p) b)).take i) • ⊤ :
      Submodule (MvPolynomial σ A) (MvPolynomial σ A)) =
      deltaRootSubsetRelationIdeal (p := p) {s | s ∈ l.take i} b := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← List.map_take,
      deltaRootRelation_ofList_eq_subset]
  rw [hI, List.getElem_map]
  exact hr

/-- Fin nで指定した異なる根関係の有限族は弱正則列。 -/
theorem deltaRootRelation_fin_isWeaklyRegular_of_ne_zero (hp : p ≠ 0)
    (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (List.ofFn fun i ↦ deltaRootRelationFamily (p := p) b (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    deltaRootRelation_list_isWeaklyRegular_of_ne_zero hp b (List.ofFn s)
      (List.nodup_ofFn_ofInjective hs)

/-- 異なる有限個の根関係のKoszul複体は、実際の通常商の分解。 -/
theorem deltaRootRelation_fin_isKoszulResolution_of_ne_zero (hp : p ≠ 0)
    (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution
      (fun i ↦ deltaRootRelationFamily (p := p) b (s i)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaRootRelation_fin_isWeaklyRegular_of_ne_zero hp b s hs)

/-- 任意の係数変更後も、異なる有限根関係の標準像は実Koszul分解を与える。 -/
theorem deltaRootRelation_map_fin_isKoszulResolution_of_ne_zero (hp : p ≠ 0)
    {B : Type w} [CommRing B] (f : A →+* B) (b : σ → A)
    {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution
      (fun i ↦ MvPolynomial.map f (deltaRootRelationFamily (p := p) b (s i))) := by
  simpa only [deltaRootRelationFamily, map_sub, map_pow, MvPolynomial.map_X,
    MvPolynomial.map_C] using
    deltaRootRelation_fin_isKoszulResolution_of_ne_zero hp (fun t ↦ f (b t)) s hs


/-- 異なる有限個の根関係は、任意係数環上の弱正則列。 -/
theorem deltaRootRelation_list_isWeaklyRegular [Fact p.Prime]
    (b : σ → A) (l : List σ) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (l.map (deltaRootRelationFamily (p := p) b)) :=
  deltaRootRelation_list_isWeaklyRegular_of_ne_zero (Fact.out : p.Prime).ne_zero b l hl

/-- Fin nで指定した異なる根関係の有限族は弱正則列。 -/
theorem deltaRootRelation_fin_isWeaklyRegular [Fact p.Prime]
    (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (List.ofFn fun i ↦ deltaRootRelationFamily (p := p) b (s i)) :=
  deltaRootRelation_fin_isWeaklyRegular_of_ne_zero (Fact.out : p.Prime).ne_zero b s hs

/-- 異なる有限個の根関係のKoszul複体は、実際の通常商の分解。 -/
theorem deltaRootRelation_fin_isKoszulResolution [Fact p.Prime]
    (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution
      (fun i ↦ deltaRootRelationFamily (p := p) b (s i)) :=
  deltaRootRelation_fin_isKoszulResolution_of_ne_zero (Fact.out : p.Prime).ne_zero b s hs

/-- 任意の係数変更後も、異なる有限根関係の標準像は実Koszul分解を与える。 -/
theorem deltaRootRelation_map_fin_isKoszulResolution [Fact p.Prime]
    {B : Type w} [CommRing B] (f : A →+* B) (b : σ → A)
    {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution
      (fun i ↦ MvPolynomial.map f (deltaRootRelationFamily (p := p) b (s i))) :=
  deltaRootRelation_map_fin_isKoszulResolution_of_ne_zero (Fact.out : p.Prime).ne_zero f b s hs

end SerrePositivity.BhattScholze

end DeltaRootFiniteRegularSequence

/-! ## 部分根関係の商の標準係数射に関する自由性・忠実平坦性

任意添字集合と零係数環を含む。実完備化後の完全忠実平坦性は別工程。
-/

@[expose] public noncomputable section DeltaRootSubsetFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A] {σ : Type v}
variable (T : Set σ) (b : σ → A)

/-- 部分根関係の商表示は標準A代数構造と両立する。 -/
def deltaRootSubsetQuotientAlgEquiv :
    (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b) ≃ₐ[A]
      MvPolynomial (Tᶜ : Set σ) (MonicPowerFamilyCover p T A (fun s ↦ b s)) := by
  apply AlgEquiv.ofRingEquiv (f := deltaRootSubsetQuotientEquiv (p := p) T b)
  intro a
  exact deltaRootSubsetQuotientEquiv_C T b a

/-- 任意部分集合の根関係の商は、標準係数射でA上自由。 -/
theorem deltaRootSubsetQuotient_moduleFree [Fact p.Prime] :
    Module.Free A (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b) := by
  let := monicPowerFamilyPolynomial_moduleFree p T (Tᶜ : Set σ) A
    (fun s ↦ b s) (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv (deltaRootSubsetQuotientAlgEquiv T b).symm.toLinearEquiv

/-- 任意部分集合の根関係の商は、標準係数射でA上忠実平坦。零環も含む。 -/
theorem deltaRootSubsetQuotient_moduleFaithfullyFlat [Fact p.Prime] :
    Module.FaithfullyFlat A
      (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b) := by
  let := monicPowerFamilyPolynomial_moduleFaithfullyFlat p T (Tᶜ : Set σ) A
    (fun s ↦ b s) (Fact.out : p.Prime).pos
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaRootSubsetQuotientAlgEquiv T b).toLinearEquiv

/-- 部分根関係の商はA上平坦。 -/
theorem deltaRootSubsetQuotient_moduleFlat [Fact p.Prime] :
    Module.Flat A (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b) := by
  let := deltaRootSubsetQuotient_moduleFaithfullyFlat (p := p) T b
  infer_instance

end SerrePositivity.BhattScholze

end DeltaRootSubsetFlat

/-! ## 有限根関係の実商の係数側Tor

標準係数射A→商についてのTorと、源多項式環への平坦係数拡大後のTorを計算する。
(p,d)のKoszul複体自体の次数零集中とは区別する。
-/

@[expose] public noncomputable section DeltaRootFiniteTor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A σ : Type u} [CommRing A]
variable (b : σ → A) {n : ℕ} (s : Fin n → σ)

/-- 有限根関係の実生成イデアルは、添字の像の部分集合イデアル。 -/
theorem deltaRootFiniteRelationIdeal_eq_subset :
    Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i)) =
      deltaRootSubsetRelationIdeal (p := p) (Set.range s) b := by
  unfold deltaRootSubsetRelationIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨s i, ⟨i, rfl⟩⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := t.property
    exact ⟨i, congrArg (deltaRootRelationFamily (p := p) b) hi⟩

/-- 有限根関係の実商は、標準係数射によってA上平坦。添字の単射性は不要。 -/
theorem deltaRootFiniteQuotient_moduleFlat [Fact p.Prime] :
    Module.Flat A (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i))) := by
  rw [deltaRootFiniteRelationIdeal_eq_subset]
  exact deltaRootSubsetQuotient_moduleFlat (p := p) (Set.range s) b

/-- 有限根関係の実商は、標準係数射によってA上忠実平坦。零係数環も含む。 -/
theorem deltaRootFiniteQuotient_moduleFaithfullyFlat [Fact p.Prime] :
    Module.FaithfullyFlat A (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i))) := by
  rw [deltaRootFiniteRelationIdeal_eq_subset]
  exact deltaRootSubsetQuotient_moduleFaithfullyFlat (p := p) (Set.range s) b

/-- 任意係数加群Nとの高次Torは零。既存Torを具体的な有限商へ適用する。 -/
theorem deltaRootFiniteQuotient_tor_subsingleton [Fact p.Prime]
    (N : Type u) [AddCommGroup N] [Module A N] (i : ℕ) :
    Subsingleton (TorModule A (i + 1) (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i))) N) := by
  let := deltaRootFiniteQuotient_moduleFlat (p := p) b s
  exact torModule_subsingleton_of_flat _ N i

/-- 任意係数加群Nとの実導来テンソルは次数零に集中する。 -/
theorem deltaRootFiniteQuotient_derivedTensor_concentrated [Fact p.Prime]
    (N : Type u) [AddCommGroup N] [Module A N] :
    IsConcentratedInDegreeZero (derivedTensor A (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i))) N) := by
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact deltaRootFiniteQuotient_tor_subsingleton b s N i

/-- 源多項式環へ係数拡大した任意加群に対しても、実商との高次Torは零。 -/
theorem deltaRootFiniteQuotient_tor_baseChange_subsingleton [Fact p.Prime]
    (N : Type u) [AddCommGroup N] [Module A N] (i : ℕ) :
    Subsingleton (TorModule (MvPolynomial σ A) (i + 1) (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i)))
      (TensorProduct A (MvPolynomial σ A) N)) := by
  exact torModule_baseChange_subsingleton A (MvPolynomial σ A) _ N (i + 1)
    (deltaRootFiniteQuotient_tor_subsingleton (p := p) b s N i)

/-- 源多項式環上での実商と係数拡大加群の導来テンソルは次数零に集中する。 -/
theorem deltaRootFiniteQuotient_derivedTensor_baseChange_concentrated [Fact p.Prime]
    (N : Type u) [AddCommGroup N] [Module A N] :
    IsConcentratedInDegreeZero (derivedTensor (MvPolynomial σ A) (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i)))
      (TensorProduct A (MvPolynomial σ A) N)) := by
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact deltaRootFiniteQuotient_tor_baseChange_subsingleton b s N i

end SerrePositivity.BhattScholze

end DeltaRootFiniteTor

/-! ## 有限根関係の係数付きKoszulホモロジー

係数環Aの任意加群Nに対し、B⊗_A N上の根関係Koszul複体を
既存の反復錐モデルとTorの自然比較で計算する。係数側(p,d)の正則性は不要。
-/

@[expose] public noncomputable section DeltaRootFiniteKoszulCoefficients

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s)
variable (N : Type u) [AddCommGroup N] [Module A N]

/-- 根関係の係数付きKoszulホモロジーと実商のTorとの既存比較の合成。 -/
def deltaRootFiniteKoszulCoefficientTorEquiv (i : ℕ) :
    (((koszulModuleFunctor (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).homology
      (-(i : ℤ))) ≃ₗ[MvPolynomial σ A]
      TorModule (MvPolynomial σ A) i (MvPolynomial σ A ⧸
        Ideal.span (Set.range fun j ↦ deltaRootRelationFamily (p := p) b (s j)))
        (TensorProduct A (MvPolynomial σ A) N) :=
  (((koszulModuleTorComparison (fun j ↦ deltaRootRelationFamily (p := p) b (s j))
    (deltaRootRelation_fin_isKoszulResolution b s hs) i).app
    (ModuleCat.of (MvPolynomial σ A)
      (TensorProduct A (MvPolynomial σ A) N))).symm.toLinearEquiv).trans
    (torModuleComm i (TensorProduct A (MvPolynomial σ A) N) _)

/-- 零次数ホモロジーは、実根関係商と係数加群の通常テンソル積。 -/
def deltaRootFiniteKoszulCoefficientHomologyZeroEquiv :
    (((koszulModuleFunctor (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).homology 0)
      ≃ₗ[MvPolynomial σ A] TensorProduct A (MvPolynomial σ A ⧸
        Ideal.span (Set.range fun j ↦ deltaRootRelationFamily (p := p) b (s j))) N :=
  ((deltaRootFiniteKoszulCoefficientTorEquiv b s hs N 0).trans
    (torModuleZeroEquiv (MvPolynomial σ A) _ _)).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A (MvPolynomial σ A) (MvPolynomial σ A) _ N)

include hs

/-- 任意係数加群を拡大した根関係Koszul複体の負次数ホモロジーは零加群。 -/
theorem deltaRootFiniteKoszulCoefficientHomology_subsingleton (i : ℕ) :
    Subsingleton (((koszulModuleFunctor
      (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).homology
      (-((i + 1 : ℕ) : ℤ))) := by
  let := deltaRootFiniteQuotient_tor_baseChange_subsingleton (p := p) b s N i
  exact (deltaRootFiniteKoszulCoefficientTorEquiv b s hs N (i + 1)).injective.subsingleton

/-- 同じ消滅を共通の圏論的IsZeroで供給する。 -/
theorem deltaRootFiniteKoszulCoefficientHomology_isZero (i : ℕ) :
    IsZero (((koszulModuleFunctor
      (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).homology
      (-((i + 1 : ℕ) : ℤ))) := by
  let := deltaRootFiniteKoszulCoefficientHomology_subsingleton (p := p) b s hs N i
  exact ModuleCat.isZero_of_subsingleton _

/-- 任意係数イデアルIの通常商を係数としても負次数Koszulホモロジーは零。 -/
theorem deltaRootFiniteKoszulQuotientCoefficientHomology_isZero
    (I : Ideal A) (i : ℕ) :
    IsZero (((koszulModuleFunctor
      (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A)
        (TensorProduct A (MvPolynomial σ A) (A ⧸ I)))).homology
      (-((i + 1 : ℕ) : ℤ))) :=
  deltaRootFiniteKoszulCoefficientHomology_isZero b s hs (A ⧸ I) i

end SerrePositivity.BhattScholze

end DeltaRootFiniteKoszulCoefficients

/-! ## 根関係の係数付きKoszul複体から実商への擬同型

既存反復錐複体と実際の(Q⊗_A N)[0]の間の写像を供給する。
係数側(p,d)の正則性・係数加群の平坦性は不要。
-/

@[expose] public noncomputable section DeltaRootFiniteKoszulAugmentation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s)
variable (N : Type u) [AddCommGroup N] [Module A N]

include hs in
/-- 根関係の係数付きKoszul複体は、すべての非零次数でホモロジーが零。 -/
theorem deltaRootFiniteKoszulCoefficientHomology_isZero_of_ne (k : ℤ) (hk : k ≠ 0) :
    IsZero (((koszulModuleFunctor
      (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).homology k) := by
  cases k with
  | ofNat i =>
      have hn : i ≠ 0 := by
        intro h
        subst i
        exact hk rfl
      have hi : 0 < (i : ℤ) := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hn)
      exact isZero_homology_of_isZero_X _ _
        (koszulModuleFunctor_isZero_X_of_pos
          (fun j ↦ deltaRootRelationFamily (p := p) b (s j))
          (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N)) (i : ℤ) hi)
  | negSucc i =>
      simpa only [Int.natCast_add, Int.natCast_one, Int.negSucc_eq] using
        deltaRootFiniteKoszulCoefficientHomology_isZero (p := p) b s hs N i

omit [Fact p.Prime] in
/-- 根関係の係数付きKoszul複体の零次数から一次数への微分は零。 -/
theorem deltaRootFiniteKoszulCoefficient_d_zero :
    ((koszulModuleFunctor (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).d 0 1 = 0 :=
  (koszulModuleFunctor_isZero_X_of_pos _ _ 1 (by decide)).eq_of_tgt _ _

/-- 係数付き根関係Koszul複体から実通常テンソル積の単一複体への具体的写像。 -/
def deltaRootFiniteKoszulCoefficientAugmentation :
    (koszulModuleFunctor (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N)) ⟶
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A ⧸
        Ideal.span (Set.range fun j ↦ deltaRootRelationFamily (p := p) b (s j))) N)) :=
  toSingleOfHomology _ (deltaRootFiniteKoszulCoefficient_d_zero b s N)
    (deltaRootFiniteKoszulCoefficientHomologyZeroEquiv b s hs N).toModuleIso.hom

/-- 具体的な係数付き根関係添加写像は擬同型。 -/
theorem deltaRootFiniteKoszulCoefficientAugmentation_quasiIso :
    QuasiIso (deltaRootFiniteKoszulCoefficientAugmentation (p := p) b s hs N) :=
  quasiIso_toSingleOfHomology _ (deltaRootFiniteKoszulCoefficient_d_zero b s N)
    (deltaRootFiniteKoszulCoefficientHomologyZeroEquiv b s hs N).toModuleIso.hom
    (deltaRootFiniteKoszulCoefficientHomology_isZero_of_ne b s hs N)

/-- 添加写像の零次ホモロジー射は、既存Tor比較から得た具体的な零次同型。 -/
theorem deltaRootFiniteKoszulCoefficientAugmentation_homologyMap :
    HomologicalComplex.homologyMap
      (deltaRootFiniteKoszulCoefficientAugmentation (p := p) b s hs N) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A ⧸
          Ideal.span (Set.range fun j ↦ deltaRootRelationFamily (p := p) b (s j))) N))).hom =
      (deltaRootFiniteKoszulCoefficientHomologyZeroEquiv b s hs N).toModuleIso.hom :=
  toSingleOfHomology_homologyMap _ (deltaRootFiniteKoszulCoefficient_d_zero b s N) _

end SerrePositivity.BhattScholze

end DeltaRootFiniteKoszulAugmentation

/-! ## 有限根関係と係数側Koszul操作の相対比較

係数側の列は任意であり、p,dの正則性やそのKoszul複体の次数零集中は仮定しない。
-/

@[expose] public noncomputable section DeltaRootRelativeKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s)
variable (N : Type u) [AddCommGroup N] [Module A N]

/-- 根関係の実添加写像に係数側の有限Koszul操作を施した具体的な写像。 -/
def deltaRootFiniteRelativeKoszulAugmentation {m : ℕ} (a : Fin m → A) :
    koszulComplexOn (fun i ↦ MvPolynomial.C (a i))
      ((koszulModuleFunctor (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
        (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))) ⟶
    koszulComplexOn (fun i ↦ MvPolynomial.C (a i))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A ⧸
          Ideal.span (Set.range fun j ↦ deltaRootRelationFamily (p := p) b (s j))) N))) :=
  (koszulFunctor (fun i ↦ MvPolynomial.C (a i))).map
    (deltaRootFiniteKoszulCoefficientAugmentation (p := p) b s hs N)

/-- 係数側の任意有限列での相対添加写像は擬同型。係数列の正則性は不要。 -/
theorem deltaRootFiniteRelativeKoszulAugmentation_quasiIso {m : ℕ} (a : Fin m → A) :
    QuasiIso (deltaRootFiniteRelativeKoszulAugmentation (p := p) b s hs N a) := by
  change QuasiIso ((koszulFunctor (fun i ↦ MvPolynomial.C (a i))).map
    (deltaRootFiniteKoszulCoefficientAugmentation (p := p) b s hs N))
  induction m with
  | zero => exact deltaRootFiniteKoszulCoefficientAugmentation_quasiIso b s hs N
  | succ m ih =>
      let : QuasiIso ((koszulFunctor
          (Fin.init (fun i ↦ MvPolynomial.C (a i)))).map
          (deltaRootFiniteKoszulCoefficientAugmentation (p := p) b s hs N)) := ih (Fin.init a)
      exact DerivedCompletion.scalarConeFunctor_map_quasiIso (MvPolynomial σ A)
        (MvPolynomial.C (a (Fin.last m))) _

/-- 特に係数側のp,dのKoszul操作を伴う実相対比較は擬同型。 -/
theorem deltaRootFiniteRelativeKoszulAugmentation_pd_quasiIso (d : A) :
    QuasiIso (deltaRootFiniteRelativeKoszulAugmentation (p := p) b s hs N ![(p : A), d]) :=
  deltaRootFiniteRelativeKoszulAugmentation_quasiIso b s hs N _

end SerrePositivity.BhattScholze

end DeltaRootRelativeKoszul

/-! ## 根関係の具体的係数商の標準射・自由性・忠実平坦性 -/

@[expose] public noncomputable section DeltaRootRelationCoefficientFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (d : A) (b : σ → A)

/-- A/(p,d)から根関係の具体的係数商への標準係数射。 -/
def deltaRootRelationCoefficientBaseMap :
    A ⧸ Ideal.span {(p : A), d} →+* DeltaRootRelationCoefficientQuotient (p := p) d b :=
  (deltaRootRelationCoefficientPowerEquiv (p := p) d b).symm.toRingHom.comp
    (algebraMap (A ⧸ Ideal.span {(p : A), d})
      (MonicPowerFamilyCover p σ (A ⧸ Ideal.span {(p : A), d})
        (fun s => Ideal.Quotient.mk _ (b s))))

omit [Fact p.Prime] in
/-- 標準係数射は元の係数の商像に一致する。 -/
theorem deltaRootRelationCoefficientBaseMap_mk (c : A) :
    deltaRootRelationCoefficientBaseMap (p := p) d b (Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk _ (MvPolynomial.C c) := by
  apply (deltaRootRelationCoefficientPowerEquiv (p := p) d b).injective
  change (deltaRootRelationCoefficientPowerEquiv (p := p) d b)
    ((deltaRootRelationCoefficientPowerEquiv (p := p) d b).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaRootRelationCoefficientPowerEquiv_C]

/-- 標準係数射による根関係係数商の代数構造。 -/
@[instance_reducible] def deltaRootRelationCoefficientBaseAlgebra :
    Algebra (A ⧸ Ideal.span {(p : A), d}) (DeltaRootRelationCoefficientQuotient (p := p) d b) :=
  (deltaRootRelationCoefficientBaseMap (p := p) d b).toAlgebra

/-- 根関係の係数商比較は標準係数射に関する代数同型。 -/
def deltaRootRelationCoefficientPowerAlgEquiv :
    letI := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
    DeltaRootRelationCoefficientQuotient (p := p) d b ≃ₐ[A ⧸ Ideal.span {(p : A), d}]
      MonicPowerFamilyCover p σ (A ⧸ Ideal.span {(p : A), d})
        (fun s => Ideal.Quotient.mk _ (b s)) := by
  letI := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
  apply AlgEquiv.ofRingEquiv (f := deltaRootRelationCoefficientPowerEquiv (p := p) d b)
  intro c
  exact (deltaRootRelationCoefficientPowerEquiv (p := p) d b).apply_symm_apply _

/-- 根関係の係数商は標準射によってA/(p,d)上自由。 -/
theorem deltaRootRelationCoefficient_moduleFree :
    letI := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
    Module.Free (A ⧸ Ideal.span {(p : A), d})
      (DeltaRootRelationCoefficientQuotient (p := p) d b) := by
  let := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
  let := monicPowerFamilyCover_moduleFree p σ (A ⧸ Ideal.span {(p : A), d})
    (fun s => Ideal.Quotient.mk _ (b s)) (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv
    (deltaRootRelationCoefficientPowerAlgEquiv (p := p) d b).symm.toLinearEquiv

/-- 根関係の係数商は標準射によってA/(p,d)上忠実平坦。零係数商も含む。 -/
theorem deltaRootRelationCoefficient_moduleFaithfullyFlat :
    letI := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d})
      (DeltaRootRelationCoefficientQuotient (p := p) d b) := by
  let := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all p σ (A ⧸ Ideal.span {(p : A), d})
    (fun s => Ideal.Quotient.mk _ (b s)) (Fact.out : p.Prime).pos
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaRootRelationCoefficientPowerAlgEquiv (p := p) d b).toLinearEquiv

/-- 根関係の係数商は標準射によってA/(p,d)上平坦。 -/
theorem deltaRootRelationCoefficient_moduleFlat :
    letI := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
    Module.Flat (A ⧸ Ideal.span {(p : A), d})
      (DeltaRootRelationCoefficientQuotient (p := p) d b) := by
  let := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
  let := deltaRootRelationCoefficient_moduleFaithfullyFlat (p := p) d b
  infer_instance

omit [Fact p.Prime] in
/-- 係数商内で各変数のp乗は指定した元の標準像に一致する。 -/
theorem deltaRootRelationCoefficient_variable_pow (s : σ) :
    (Ideal.Quotient.mk
      (deltaDivisionFirstBaseIdeal (p := p) (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b))
      (MvPolynomial.X s)) ^ p =
      deltaRootRelationCoefficientBaseMap (p := p) d b (Ideal.Quotient.mk _ (b s)) := by
  apply (deltaRootRelationCoefficientPowerEquiv (p := p) d b).injective
  rw [deltaRootRelationCoefficientBaseMap_mk, map_pow,
    deltaRootRelationCoefficientPowerEquiv_X, deltaRootRelationCoefficientPowerEquiv_C,
    monicPowerFamilyRoot_pow]

end SerrePositivity.BhattScholze

end DeltaRootRelationCoefficientFlat

/-! ## 根添加を入れた具体的δ除算包のraw残余商 -/

@[expose] public noncomputable section DeltaRootAdjoinDivisionResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- rank-one多項式δ環でCdにより根関係を除算した既存添加環のraw残余商。 -/
abbrev DeltaRootAdjoinDivisionResidue :=
  DeltaAdjoinDivisionResidue (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
    (deltaRootRelationFamily (p := p) b)

/-- 根を表す元は、源多項式変数の既存δ係数射による標準残余商像。 -/
def deltaRootAdjoinDivisionResidueVariable (s : σ) : DeltaRootAdjoinDivisionResidue D d b :=
  Ideal.Quotient.mk _ (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D)
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b) (MvPolynomial.X s))

/-- 基底のδdを表す単元は、源rank-one多項式δ環のCdのδ値を表す。 -/
theorem deltaRootPolynomialUnit_delta (u : Aˣ) (hu : (u : A) = D.delta d) :
    ((u.map (MvPolynomial.C : A →+* MvPolynomial σ A) : (MvPolynomial σ A)ˣ) :
      MvPolynomial σ A) = (polynomialRankOneDeltaStructure σ D).delta (MvPolynomial.C d) := by
  change MvPolynomial.C (u : A) = _
  rw [hu, polynomialRankOneDeltaStructure_delta_C]

variable (hpB : Function.Injective (fun f : MvPolynomial σ A => (p : MvPolynomial σ A) * f))
variable (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := MvPolynomial σ A) σ =>
  (p : RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) * f))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (u : Aˣ) (hu : (u : A) = D.delta d)

/-- A/(p,d)から根添加を入れたrawδ除算残余商への具体的標準係数射。 -/
def deltaRootAdjoinDivisionResidueBaseMap :
    A ⧸ Ideal.span {(p : A), d} →+* DeltaRootAdjoinDivisionResidue D d b :=
  (deltaAdjoinDivisionResidueBaseMap (polynomialRankOneDeltaStructure σ D) hpB hpL hg
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b)
    (u.map (MvPolynomial.C : A →+* MvPolynomial σ A))
    (deltaRootPolynomialUnit_delta D d u hu)).comp
    (deltaRootRelationCoefficientBaseMap (p := p) d b)

/-- 標準係数射は源多項式環の基底係数の既存δ係数射の残余商像に一致する。 -/
theorem deltaRootAdjoinDivisionResidueBaseMap_mk (c : A) :
    deltaRootAdjoinDivisionResidueBaseMap D d b hpB hpL hg u hu (Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D)
        (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b) (MvPolynomial.C c)) := by
  rw [deltaRootAdjoinDivisionResidueBaseMap, RingHom.comp_apply,
    deltaRootRelationCoefficientBaseMap_mk, deltaAdjoinDivisionResidueBaseMap_mk]

/-- 標準係数射による根δ除算残余商のA/(p,d)代数構造。 -/
@[instance_reducible] def deltaRootAdjoinDivisionResidueBaseAlgebra :
    Algebra (A ⧸ Ideal.span {(p : A), d}) (DeltaRootAdjoinDivisionResidue D d b) :=
  (deltaRootAdjoinDivisionResidueBaseMap D d b hpB hpL hg u hu).toAlgebra

/-- 根添加を入れたrawδ除算残余商は標準係数射によってA/(p,d)上忠実平坦。 -/
theorem deltaRootAdjoinDivisionResidue_moduleFaithfullyFlat :
    letI := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpB hpL hg u hu
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d}) (DeltaRootAdjoinDivisionResidue D d b) := by
  let := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
  let := deltaAdjoinDivisionResidueBaseAlgebra (polynomialRankOneDeltaStructure σ D) hpB hpL hg
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b)
    (u.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (deltaRootPolynomialUnit_delta D d u hu)
  let := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpB hpL hg u hu
  let : IsScalarTower (A ⧸ Ideal.span {(p : A), d})
      (DeltaRootRelationCoefficientQuotient (p := p) d b)
      (DeltaRootAdjoinDivisionResidue D d b) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := deltaRootRelationCoefficient_moduleFaithfullyFlat (p := p) d b
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat (polynomialRankOneDeltaStructure σ D)
    hpB hpL hg (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b)
    (u.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (deltaRootPolynomialUnit_delta D d u hu)
  exact Module.FaithfullyFlat.trans _ (DeltaRootRelationCoefficientQuotient (p := p) d b) _

/-- 根添加を入れたrawδ除算残余商は標準係数射によってA/(p,d)上平坦。 -/
theorem deltaRootAdjoinDivisionResidue_moduleFlat :
    letI := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpB hpL hg u hu
    Module.Flat (A ⧸ Ideal.span {(p : A), d}) (DeltaRootAdjoinDivisionResidue D d b) := by
  let := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpB hpL hg u hu
  let := deltaRootAdjoinDivisionResidue_moduleFaithfullyFlat D d b hpB hpL hg u hu
  infer_instance

/-- rawδ除算残余商の具体的な根は、指定元の標準像をp乗根として持つ。 -/
theorem deltaRootAdjoinDivisionResidueVariable_pow (s : σ) :
    deltaRootAdjoinDivisionResidueVariable D d b s ^ p =
      deltaRootAdjoinDivisionResidueBaseMap D d b hpB hpL hg u hu (Ideal.Quotient.mk _ (b s)) := by
  let q := deltaAdjoinDivisionResidueBaseMap (polynomialRankOneDeltaStructure σ D) hpB hpL hg
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b)
    (u.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (deltaRootPolynomialUnit_delta D d u hu)
  have h := congrArg q (deltaRootRelationCoefficient_variable_pow (p := p) d b s)
  rw [map_pow, deltaAdjoinDivisionResidueBaseMap_mk] at h
  exact h

end SerrePositivity.BhattScholze

end DeltaRootAdjoinDivisionResidue

/-! ## 根δ除算添加環の源変数のrank-one性と実際の根関係 -/

@[expose] public noncomputable section DeltaRootAdjoinDivisionVariables

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- 既存rank-one多項式δ環の根関係をCdでδ除算した実際のraw環。 -/
abbrev DeltaRootAdjoinDivision :=
  DeltaAdjoinDivision (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
    (deltaRootRelationFamily (p := p) b)

/-- raw環内の源多項式変数の標準δ係数像。 -/
def deltaRootAdjoinDivisionVariable (s : σ) : DeltaRootAdjoinDivision D d b :=
  deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
    (deltaRootRelationFamily (p := p) b) (MvPolynomial.X s)

/-- raw環内の根変数のδ値は零。残余商のδ構造は仮定しない。 -/
theorem deltaRootAdjoinDivisionVariable_delta (s : σ) :
    (deltaAdjoinDivisionStructure (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b)).delta
        (deltaRootAdjoinDivisionVariable D d b s) = 0 := by
  have h := deltaAdjoinDivisionMap_isDeltaHom (polynomialRankOneDeltaStructure σ D)
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b) (MvPolynomial.X s)
  rw [polynomialRankOneDeltaStructure_delta_X, map_zero] at h
  exact h.symm

/-- raw環内の根変数のp乗と指定元の像の差は、dの像と除算変数の積。 -/
theorem deltaRootAdjoinDivisionVariable_pow (s : σ) :
    deltaRootAdjoinDivisionVariable D d b s ^ p =
      deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (deltaRootRelationFamily (p := p) b) (MvPolynomial.C (b s)) +
      deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (deltaRootRelationFamily (p := p) b) (MvPolynomial.C d) *
      deltaAdjoinDivisionVariable (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (deltaRootRelationFamily (p := p) b) s := by
  have h := deltaAdjoinDivision_relation (polynomialRankOneDeltaStructure σ D)
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b) s
  change _ = deltaAdjoinDivisionMap _ _ _ (MvPolynomial.X s ^ p - MvPolynomial.C (b s)) at h
  rw [map_sub, map_pow] at h
  exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)

/-- dの像を消す任意通常環射の先で、源変数の像は指定元のp乗根。 -/
theorem deltaRootAdjoinDivisionVariable_map_pow {T : Type w} [CommRing T]
    (q : DeltaRootAdjoinDivision D d b →+* T)
    (hd : q (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b) (MvPolynomial.C d)) = 0) (s : σ) :
    q (deltaRootAdjoinDivisionVariable D d b s) ^ p =
      q (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (deltaRootRelationFamily (p := p) b) (MvPolynomial.C (b s))) := by
  have h := congrArg q (deltaRootAdjoinDivisionVariable_pow D d b s)
  simpa only [map_pow, map_add, map_mul, hd, zero_mul, add_zero] using h

end SerrePositivity.BhattScholze

end DeltaRootAdjoinDivisionVariables

/-! ## 先行根関係のp乗商における後続根関係の正則性

標数pでは先行関係のp乗は指数p²のモニック根関係である。
既存の任意部分集合商の多項式表示を再利用する。
-/

@[expose] public noncomputable section DeltaRootPowerSubsetRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 標数pの先行根関係のp乗イデアルは、指数p²の既存根関係イデアル。 -/
theorem deltaRootSubset_powerRelationIdeal_eq (hp : (p : A) = 0) (T : Set σ) (b : σ → A) :
    Ideal.span (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p) =
      deltaRootSubsetRelationIdeal (p := p * p) T (fun s ↦ b s ^ p) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := hA
    exact Subsingleton.elim _ _
  · have := hA
    have : CharP A p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    unfold deltaRootSubsetRelationIdeal
    congr 1
    congr 1
    funext t
    simp only [deltaRootRelationFamily, sub_pow_char, ← pow_mul, ← map_pow]

/-- 先行根関係のp乗で割った後も、残りの根関係は正則。先行集合の有限性は不要。 -/
theorem deltaRootSubsetPowerQuotient_remaining_isSMulRegular
    (hp : (p : A) = 0) (T : Set σ) (b : σ → A) (s : σ) (hs : s ∉ T) :
    IsSMulRegular
      (MvPolynomial σ A ⧸ Ideal.span
        (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p))
      (Ideal.Quotient.mk
        (Ideal.span (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p))
        (deltaRootRelationFamily (p := p) b s)) := by
  rw [deltaRootSubset_powerRelationIdeal_eq hp]
  let e := deltaRootSubsetQuotientEquiv (p := p * p) T (fun t ↦ b t ^ p)
  let C := MonicPowerFamilyCover (p * p) T A (fun t ↦ b t ^ p)
  have he : e (Ideal.Quotient.mk _ (deltaRootRelationFamily (p := p) b s)) =
      deltaRootRelationFamily (p := p)
        (fun t : (Tᶜ : Set σ) ↦ algebraMap A C (b t)) ⟨s, hs⟩ := by
    simp only [deltaRootRelationFamily, map_sub, map_pow, e,
      deltaRootSubsetQuotientEquiv_C]
    rw [deltaRootSubsetQuotientEquiv_X_notMem T (fun t ↦ b t ^ p) ⟨s, hs⟩]
  have hr := deltaRootRelation_isSMulRegular (p := p)
    (fun t : (Tᶜ : Set σ) ↦ algebraMap A C (b t)) (⟨s, hs⟩ : (Tᶜ : Set σ))
  intro x y hxy
  apply e.injective
  apply hr
  have h := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using h

end SerrePositivity.BhattScholze

end DeltaRootPowerSubsetRegular

/-! ## 先行根関係のp乗商と係数商の標準比較 -/

@[expose] public noncomputable section DeltaRootPowerSubsetBaseQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (I : Ideal A) (T : Set σ) (b : σ → A)
local notation "J" => Ideal.span (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p)
local notation "Jbar" => Ideal.span (Set.range fun t : T ↦
  (deltaRootRelationFamily (p := p) (fun s ↦ Ideal.Quotient.mk I (b s)) t) ^ p)
local notation "IB" => I.map (MvPolynomial.C : A →+* MvPolynomial σ A)

omit [Fact p.Prime] in
/-- 先行根関係のp乗イデアルは係数商の下で対応するイデアルに写る。 -/
theorem deltaRootPowerSubsetIdeal_map_coefficientQuotient :
    ((J).map (Ideal.Quotient.mk IB)).map
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom = Jbar := by
  rw [Ideal.map_map, monicPowerFamilyCoefficientQuotient_comp]
  simp only [Ideal.map_span, ← Set.range_comp', deltaRootRelationFamily,
    map_pow, map_sub, MvPolynomial.map_X, MvPolynomial.map_C]

/-- 係数イデアルと先行根関係のp乗による商の具体的な標準同型。 -/
def deltaRootPowerSubsetBaseQuotientEquiv :
    (MvPolynomial σ A ⧸ (IB ⊔ J)) ≃+* (MvPolynomial σ (A ⧸ I) ⧸ Jbar) :=
  (DoubleQuot.quotQuotEquivQuotSup IB J).symm.trans
    (Ideal.quotientEquiv _ _
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingEquiv
      (deltaRootPowerSubsetIdeal_map_coefficientQuotient (p := p) I T b).symm)

omit [Fact p.Prime] in
/-- 標準同型は多項式の係数を商へ送る写像で与えられる。 -/
theorem deltaRootPowerSubsetBaseQuotientEquiv_mk (x : MvPolynomial σ A) :
    deltaRootPowerSubsetBaseQuotientEquiv (p := p) I T b (Ideal.Quotient.mk (IB ⊔ J) x) =
      Ideal.Quotient.mk Jbar (MvPolynomial.map (Ideal.Quotient.mk I) x) := by
  change Ideal.Quotient.mk Jbar
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm
      (Ideal.Quotient.mk IB x)) = _
  congr 1
  exact DFunLike.congr_fun (monicPowerFamilyCoefficientQuotient_comp σ A I) x

/-- pと先行根関係のp乗で割っても、残りの根関係は正則。 -/
theorem deltaRootPowerSubsetModP_remaining_isSMulRegular
    (T : Set σ) (b : σ → A) (s : σ) (hs : s ∉ T) :
    IsSMulRegular
      (MvPolynomial σ A ⧸ (Ideal.span {(p : MvPolynomial σ A)} ⊔
        Ideal.span (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p)))
      (Ideal.Quotient.mk
        (Ideal.span {(p : MvPolynomial σ A)} ⊔
          Ideal.span (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p))
        (deltaRootRelationFamily (p := p) b s)) := by
  let I := Ideal.span {(p : A)}
  let e := deltaRootPowerSubsetBaseQuotientEquiv (p := p) I T b
  have hp : (p : A ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hr := deltaRootSubsetPowerQuotient_remaining_isSMulRegular hp T
    (fun t ↦ Ideal.Quotient.mk I (b t)) s hs
  have he : e (Ideal.Quotient.mk _ (deltaRootRelationFamily (p := p) b s)) =
      Ideal.Quotient.mk _
        (deltaRootRelationFamily (p := p) (fun t ↦ Ideal.Quotient.mk I (b t)) s) := by
    rw [deltaRootPowerSubsetBaseQuotientEquiv_mk]
    simp only [deltaRootRelationFamily, map_sub, map_pow, MvPolynomial.map_X,
      MvPolynomial.map_C]
  have hreg : IsSMulRegular (MvPolynomial σ A ⧸
      (I.map MvPolynomial.C ⊔ Ideal.span
        (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p)))
      (Ideal.Quotient.mk
        (I.map MvPolynomial.C ⊔ Ideal.span
          (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p))
        (deltaRootRelationFamily (p := p) b s)) := by
    intro x y hxy
    apply e.injective
    apply hr
    have h := congrArg e hxy
    simpa only [smul_eq_mul, map_mul, he] using h
  have hI : I.map (MvPolynomial.C : A →+* MvPolynomial σ A) =
      Ideal.span {(p : MvPolynomial σ A)} := by
    simp only [I, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hI] at hreg
  exact hreg

end SerrePositivity.BhattScholze

end DeltaRootPowerSubsetBaseQuotient

/-! ## 二つの独立した根関係のraw除算への正則入力 -/

@[expose] public noncomputable section DeltaRootPairInputRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 任意の根関係は、実際の多項式環のmod p商で正則。 -/
theorem deltaRootRelation_modP_isSMulRegular (b : σ → A) (s : σ) :
    IsSMulRegular (MvPolynomial σ A ⧸ Ideal.span {(p : MvPolynomial σ A)})
      (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial σ A)})
        (deltaRootRelationFamily (p := p) b s)) := by
  have h := deltaRootPowerSubsetModP_remaining_isSMulRegular (p := p) (∅ : Set σ) b s
    (by simp)
  have hJ : Set.range (fun r : (∅ : Set σ) ↦ (deltaRootRelationFamily (p := p) b r) ^ p) =
      ∅ := by
    ext z
    constructor
    · rintro ⟨r, _⟩
      exact r.property.elim
    · intro hz
      exact hz.elim
  rw [hJ, Ideal.span_empty, sup_bot_eq] at h
  exact h

/-- 異なる二つの根関係について、後者は(p,前者のp乗)の実商で正則。 -/
theorem deltaRootRelation_pairPower_modP_isSMulRegular
    (b : σ → A) (s t : σ) (hts : t ≠ s) :
    IsSMulRegular
      (MvPolynomial σ A ⧸ Ideal.span
        {(p : MvPolynomial σ A), (deltaRootRelationFamily (p := p) b s) ^ p})
      (Ideal.Quotient.mk
        (Ideal.span {(p : MvPolynomial σ A), (deltaRootRelationFamily (p := p) b s) ^ p})
        (deltaRootRelationFamily (p := p) b t)) := by
  have h := deltaRootPowerSubsetModP_remaining_isSMulRegular (p := p) ({s} : Set σ) b t
    (by simpa using hts)
  have hJ : Set.range (fun r : ({s} : Set σ) ↦ (deltaRootRelationFamily (p := p) b r) ^ p) =
      {(deltaRootRelationFamily (p := p) b s) ^ p} := by
    ext z
    constructor
    · rintro ⟨⟨r, hr⟩, rfl⟩
      have hrs : r = s := Set.mem_singleton_iff.mp hr
      subst r
      exact Set.mem_singleton _
    · intro hz
      have hz' := Set.mem_singleton_iff.mp hz
      exact ⟨⟨s, Set.mem_singleton _⟩, hz'.symm⟩
  rw [hJ, ← Ideal.span_insert] at h
  exact h

end SerrePositivity.BhattScholze

end DeltaRootPairInputRegular
