module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Regular.Basic
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaLocalization
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaAdicCompletion
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion

/-!
# d で割る δ 包 A{a_s/d}（BS 著者版 Notation 2.8 の添加の一般形）

## 概要
δ 環に a_s/d を添加した生の包 `DeltaAdjoinDivision` とその普遍性、d が正則な標的への普遍性、mod d への商射、d 冪・p 冪ねじれの δ 閉包による除去と除去商の p 正則性、古典的 (p,d) 完備化と、δ 除算・ねじれ除去・導来 (p,d) 完備化の一段操作。
δ 除算の添加、ねじれ除去、それらを合わせた普遍性は、BS 著者版 Proposition 7.2 の証明に関わる代数的な補助である。

## 方針
この構成は BS 著者版 Proposition 3.13 の prismatic envelope と Proposition 7.2 の証明で使う。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/Envelope/PDivision`、`Andre/Envelope/PDivisionSource`、`Andre/PowerRootEnvelope/DeltaDivisionResidue`、`Andre/PowerRootEnvelope/DeltaDivisionWitt`、`Andre/PowerRootEnvelope/Unconditional/Localization`、`Delta/DividedPower/PDivision`、`Delta/DividedPower/PDivisionCompletion`、`Delta/Division/Family`、`Delta/Division/Relations`、`Delta/Division/Residue`、`Semiperfectoid/PerfectPrismDivision`、`Semiperfectoid/PerfectPrismDivisionComparison`。
-/

universe u v w

/-! ## δ環でのa_s/dの添加

相対自由δ環へd*x_s=a_sの関係式を課す。BS 著者版 Notation 2.8、
BS 著者版 Proposition 7.2のJ/dのδ添加の代数的部分。d冪ねじれの除去、導来完備化、
反復構成、perfectoid化の存在はこのモジュールには含めない。
-/

@[expose] public noncomputable section DeltaAdjoinDivision

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 相対自由環でd*x_s=a_sを課す関係式のイデアル。δ安定化前の通常のイデアル。 -/
def deltaDivisionRelationIdeal (d : R) (a : σ → R) :
    Ideal (RelativeFreeDeltaRing (R := R) σ) :=
  Ideal.span (Set.range (fun s : σ ↦
    MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)))

/-- 基底δ環へa_s/dを添加する環。関係式のδ閉包で相対自由δ環を割る。 -/
abbrev DeltaAdjoinDivision (D : DeltaStructure p R) (d : R) (a : σ → R) :=
  RelativeFreeDeltaRing (R := R) σ ⧸
    (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a)

/-- a_s/dの添加環のδ構造。δ安定商の構成をそのまま使う。 -/
def deltaAdjoinDivisionStructure (D : DeltaStructure p R) (d : R) (a : σ → R) :
    DeltaStructure p (DeltaAdjoinDivision D d a) :=
  (relativeFreeDeltaStructure σ D).quotient
    ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
    ((relativeFreeDeltaStructure σ D).isStable_deltaClosure (deltaDivisionRelationIdeal d a))

/-- δ添加環への基底の標準射。係数射と商写像を合成する。 -/
def deltaAdjoinDivisionMap (D : DeltaStructure p R) (d : R) (a : σ → R) :
    R →+* DeltaAdjoinDivision D d a :=
  (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
    (deltaDivisionRelationIdeal d a))).comp MvPolynomial.C

/-- δ添加環内のa_s/dを表す初期生成元。 -/
def deltaAdjoinDivisionVariable (D : DeltaStructure p R) (d : R) (a : σ → R)
    (s : σ) : DeltaAdjoinDivision D d a :=
  Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
    (deltaDivisionRelationIdeal d a)) (MvPolynomial.X (s, 0))

/-- 基底からa_s/dのδ添加環への標準射はδ射。 -/
theorem deltaAdjoinDivisionMap_isDeltaHom (D : DeltaStructure p R) (d : R) (a : σ → R) :
    D.IsDeltaHom (deltaAdjoinDivisionStructure D d a) (deltaAdjoinDivisionMap D d a) :=
  ((relativeFreeDeltaStructure σ D).isDeltaHom_quotient_mk _
    ((relativeFreeDeltaStructure σ D).isStable_deltaClosure _)).comp
      (relativeFreeDeltaStructure_C_isDeltaHom σ D)

/-- 添加環でd*x_s=a_sが実際に成立する。指定関係式がδ閉包に含まれることを使う。 -/
theorem deltaAdjoinDivision_relation (D : DeltaStructure p R) (d : R) (a : σ → R) (s : σ) :
    deltaAdjoinDivisionMap D d a d * deltaAdjoinDivisionVariable D d a s =
      deltaAdjoinDivisionMap D d a (a s) := by
  let F := relativeFreeDeltaStructure σ D
  let I := deltaDivisionRelationIdeal d a
  let q := Ideal.Quotient.mk (F.deltaClosure I)
  change q (MvPolynomial.C d) * q (MvPolynomial.X (s, 0)) = q (MvPolynomial.C (a s))
  apply sub_eq_zero.mp
  rw [← map_mul, ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply F.le_deltaClosure I
  exact Ideal.subset_span (Set.mem_range_self s)

/-- 基底δ射fと指定した解b_sがf(d)*b_s=f(a_s)を満たせば、
δ添加環からの基底と両立するδ射が一意に存在する。p正則性やdの非零因子性は不要。 -/
theorem existsUnique_deltaAdjoinDivisionHom {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (E : DeltaStructure p A) (d : R) (a : σ → R)
    (f : R →+* A) (hf : D.IsDeltaHom E f) (b : σ → A)
    (hb : ∀ s, f d * b s = f (a s)) :
    ∃! g : DeltaAdjoinDivision D d a →+* A,
      (deltaAdjoinDivisionStructure D d a).IsDeltaHom E g ∧
        g.comp (deltaAdjoinDivisionMap D d a) = f ∧
          ∀ s, g (deltaAdjoinDivisionVariable D d a s) = b s := by
  apply existsUnique_relativeFreePresentationHom D E f hf b (deltaDivisionRelationIdeal d a)
  have hker : deltaDivisionRelationIdeal d a ≤ RingHom.ker (relativeFreeDeltaEval E f b) := by
    apply Ideal.span_le.mpr
    rintro r ⟨s, rfl⟩
    change relativeFreeDeltaEval E f b
      (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)) = 0
    rw [map_sub, map_mul, relativeFreeDeltaEval_C, relativeFreeDeltaEval_X,
      relativeFreeDeltaEval_C]
    simpa only [Function.iterate_zero_apply, sub_eq_zero] using hb s
  exact fun r hr ↦ hker hr

end SerrePositivity.BhattScholze

end DeltaAdjoinDivision

/-! ## d冪ねじれのδ閉包による商

BS 著者版 Proposition 7.2のB/B[d^∞]_δの代数的部分。
通常のd冪ねじれはMathlibの局所化射の核として扱い、新しいねじれイデアルを重複定義しない。
商の新しいdねじれの不存在や導来完備化はここでは結論しない。
-/

@[expose] public noncomputable section DeltaTorsionReduction

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- dの冪で消える元は、局所化射の核のδ閉包に属する。
BS 著者版 Proposition 7.2で旧d冪ねじれを商で消す際の具体的な包含。 -/
theorem pow_torsion_mem_deltaClosure_ker_away (D : DeltaStructure p R) (d : R)
    (N : ℕ) (x : R) (hx : d ^ N * x = 0) :
    x ∈ D.deltaClosure (RingHom.ker (algebraMap R (Localization.Away d))) := by
  apply D.le_deltaClosure
  change algebraMap R (Localization.Away d) x = 0
  apply (IsLocalization.map_eq_zero_iff (Submonoid.powers d) (Localization.Away d) x).mpr
  exact ⟨⟨d ^ N, (Submonoid.mem_powers_iff (d ^ N) d).mpr ⟨N, rfl⟩⟩, hx⟩

/-- δ射fの終域でf(d)が非零因子なら、d冪ねじれのδ閉包をfは零に送る。
局所化の核の判定、正則元の冪の消去、δ閉包の最小性を再利用する。 -/
theorem IsDeltaHom.deltaClosure_ker_away_le_ker {A : Type v} [CommRing A]
    {D : DeltaStructure p R} {E : DeltaStructure p A} {f : R →+* A}
    (hf : D.IsDeltaHom E f) (d : R)
    (hd : Function.Injective (fun x : A ↦ f d * x)) :
    D.deltaClosure (RingHom.ker (algebraMap R (Localization.Away d))) ≤ RingHom.ker f := by
  apply hf.deltaClosure_le_ker
  intro x hx
  obtain ⟨m, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers d) (Localization.Away d) x).mp hx
  obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff (m : R) d).mp m.property
  have h := congrArg f hm
  rw [← hN, map_mul, map_pow, map_zero] at h
  have hreg : IsLeftRegular (f d) := hd
  exact (IsLeftRegular.pow N hreg) (h.trans (mul_zero _).symm)

/-- δ射fがdを非零因子へ送るなら、d冪ねじれのδ閉包商から一意なδ射に降下する。
環・標準商写像・δ 構造を明示したねじれ除去段階の普遍性。 -/
theorem existsUnique_torsionReductionHom (D : DeltaStructure p R) (d : R)
    {A : Type v} [CommRing A] (E : DeltaStructure p A) (f : R →+* A)
    (hf : D.IsDeltaHom E f) (hd : Function.Injective (fun x : A ↦ f d * x)) :
    ∃! g : (R ⧸ D.deltaClosure (RingHom.ker (algebraMap R (Localization.Away d)))) →+* A,
      g.comp (Ideal.Quotient.mk
        (D.deltaClosure (RingHom.ker (algebraMap R (Localization.Away d))))) = f ∧
      (D.quotient (D.deltaClosure (RingHom.ker (algebraMap R (Localization.Away d))))
        (D.isStable_deltaClosure _)).IsDeltaHom E g :=
  D.existsUnique_quotient_lift _ (D.isStable_deltaClosure _) E f hf
    (hf.deltaClosure_ker_away_le_ker d hd)

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaTorsionReduction

/-! ## 正則なdの像へのδ除算の普遍性

BS 著者版 Proposition 7.2の代数的な二段階。指定解族を公開定理の結論から除き、
基底射・可除性・dの像の正則性から一意なδ射を得る。
導来完備化後のねじれ除去やprismの存在は結論しない。
-/

@[expose] public noncomputable section DeltaDivisionUniversal

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 添加環からの基底射と両立する射は、必ず除算の関係式を満たす。 -/
theorem deltaAdjoinDivisionHom_relation {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (d : R) (a : σ → R) (f : R →+* A)
    (g : DeltaAdjoinDivision D d a →+* A)
    (hg : g.comp (deltaAdjoinDivisionMap D d a) = f) (s : σ) :
    f d * g (deltaAdjoinDivisionVariable D d a s) = f (a s) := by
  have h := congrArg g (deltaAdjoinDivision_relation D d a s)
  rw [map_mul] at h
  have hc (r : R) : g (deltaAdjoinDivisionMap D d a r) = f r :=
    DFunLike.congr_fun hg r
  simpa only [hc] using h

/-- dの像が非零因子で、各a_sの像がdで割り切れるなら、
添加環から基底射fを延長するδ射が一意に存在する。解族の指定は不要。 -/
theorem existsUnique_deltaAdjoinDivisionHom_of_regular {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (E : DeltaStructure p A) (d : R) (a : σ → R)
    (f : R →+* A) (hf : D.IsDeltaHom E f)
    (hd : Function.Injective (fun x : A ↦ f d * x))
    (ha : ∀ s, f d ∣ f (a s)) :
    ∃! g : DeltaAdjoinDivision D d a →+* A,
      (deltaAdjoinDivisionStructure D d a).IsDeltaHom E g ∧
        g.comp (deltaAdjoinDivisionMap D d a) = f := by
  choose b hb using ha
  obtain ⟨g, hg, hu⟩ := existsUnique_deltaAdjoinDivisionHom D E d a f hf b
    (fun s ↦ (hb s).symm)
  refine ⟨g, ⟨hg.1, hg.2.1⟩, ?_⟩
  intro k hk
  apply hu k
  refine ⟨hk.1, hk.2, ?_⟩
  intro s
  apply hd
  exact (deltaAdjoinDivisionHom_relation D d a f k hk.2 s).trans (hb s)

/-- 添加環の旧d冪ねじれのδ閉包商。局所化核と既存δ閉包を使用する。 -/
abbrev DeltaDivisionTorsionQuotient (D : DeltaStructure p R) (d : R) (a : σ → R) :=
  DeltaAdjoinDivision D d a ⧸
    (deltaAdjoinDivisionStructure D d a).deltaClosure
      (RingHom.ker (algebraMap (DeltaAdjoinDivision D d a)
        (Localization.Away (deltaAdjoinDivisionMap D d a d))))

/-- 除算と旧ねじれ除去の二段階商への標準射。 -/
def deltaDivisionTorsionMap (D : DeltaStructure p R) (d : R) (a : σ → R) :
    R →+* DeltaDivisionTorsionQuotient D d a :=
  (Ideal.Quotient.mk _).comp (deltaAdjoinDivisionMap D d a)

/-- 二段階商のδ構造。 -/
def deltaDivisionTorsionStructure (D : DeltaStructure p R) (d : R) (a : σ → R) :
    DeltaStructure p (DeltaDivisionTorsionQuotient D d a) :=
  (deltaAdjoinDivisionStructure D d a).quotient _
    ((deltaAdjoinDivisionStructure D d a).isStable_deltaClosure _)

/-- 正則なdの像と可除性を持つδ基底射は、除算・旧ねじれ除去の二段階商から
一意なδ射へ延長される。完備化前の具体的な普遍性。 -/
theorem existsUnique_deltaDivisionTorsionHom {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (E : DeltaStructure p A) (d : R) (a : σ → R)
    (f : R →+* A) (hf : D.IsDeltaHom E f)
    (hd : Function.Injective (fun x : A ↦ f d * x))
    (ha : ∀ s, f d ∣ f (a s)) :
    ∃! g : DeltaDivisionTorsionQuotient D d a →+* A,
      (deltaDivisionTorsionStructure D d a).IsDeltaHom E g ∧
        g.comp (deltaDivisionTorsionMap D d a) = f := by
  let B := DeltaAdjoinDivision D d a
  let DB := deltaAdjoinDivisionStructure D d a
  let j := deltaAdjoinDivisionMap D d a
  let I := DB.deltaClosure (RingHom.ker (algebraMap B (Localization.Away (j d))))
  let q : B →+* B ⧸ I := Ideal.Quotient.mk I
  have hq := DB.isDeltaHom_quotient_mk I (DB.isStable_deltaClosure _)
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D E d a f hf hd ha
  have hkd : Function.Injective (fun x : A ↦ k (j d) * x) := by
    have h := DFunLike.congr_fun hk.2 d
    change k (j d) = f d at h
    simpa only [h] using hd
  obtain ⟨g, hg, hgu⟩ := DB.existsUnique_torsionReductionHom (j d) E k hk.1 hkd
  refine ⟨g, ⟨hg.2, ?_⟩, ?_⟩
  · change g.comp (q.comp j) = f
    rw [← RingHom.comp_assoc, hg.1, hk.2]
  · intro l hl
    have hlk : l.comp q = k := by
      apply hku (l.comp q)
      refine ⟨hl.1.comp hq, ?_⟩
      change (l.comp q).comp j = f
      rw [RingHom.comp_assoc]
      exact hl.2
    apply hgu l
    exact ⟨hlk, hl.1⟩

end SerrePositivity.BhattScholze

end DeltaDivisionUniversal

/-! ## p冪ねじれのδ安定性と除去商のp正則性

p局所化への核を再利用する。新しいねじれイデアルは定義しない。
完備化後の正則性は別工程。
-/

@[expose] public noncomputable section DeltaPTorsionReduction

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- pの冪の分母集合は任意のδ環のFrobeniusで安定。 -/
theorem powers_p_frobenius_stable (D : DeltaStructure p A)
    (s : Submonoid.powers (p : A)) : D.frobeniusLift s ∈ Submonoid.powers (p : A) := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : A) (p : A)).mp s.property
  rw [← hn, map_pow, map_natCast]
  exact Submonoid.pow_mem _ (Submonoid.mem_powers _) n

/-- p局所化への核、すなわちp冪ねじれイデアルはδ安定。 -/
theorem isStable_ker_away_p (D : DeltaStructure p A) :
    D.IsStable (RingHom.ker (algebraMap A (Localization.Away (p : A)))) :=
  (D.isDeltaHom_localization (Submonoid.powers (p : A)) (Localization.Away (p : A))
    D.powers_p_frobenius_stable).isStable_ker

/-- p冪ねじれをδ閉包してもイデアルは増えない。 -/
theorem deltaClosure_ker_away_p (D : DeltaStructure p A) :
    D.deltaClosure (RingHom.ker (algebraMap A (Localization.Away (p : A)))) =
      RingHom.ker (algebraMap A (Localization.Away (p : A))) :=
  D.deltaClosure_eq D.isStable_ker_away_p

/-- p冪ねじれのδ閉包商ではpは正則。 -/
theorem p_mul_injective_torsionReduction (D : DeltaStructure p A) :
    Function.Injective (fun x :
      A ⧸ D.deltaClosure (RingHom.ker (algebraMap A (Localization.Away (p : A)))) ↦
        (p : A ⧸ D.deltaClosure
          (RingHom.ker (algebraMap A (Localization.Away (p : A))))) * x) := by
  rw [D.deltaClosure_ker_away_p]
  let j := algebraMap A (Localization.Away (p : A))
  intro x y hxy
  apply RingHom.kerLift_injective j
  have h := congrArg (RingHom.kerLift j) hxy
  simp only [map_mul, map_natCast] at h
  have hp : IsUnit (p : Localization.Away (p : A)) := by
    simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (p : A)
  exact hp.mul_left_cancel h

/-- 除数の具体的な表示がpに等しい場合にも同じδ商のp正則性を使える。 -/
theorem p_mul_injective_torsionReduction_of_eq_p (D : DeltaStructure p A)
    (d : A) (hd : d = (p : A)) :
    Function.Injective (fun x :
      A ⧸ D.deltaClosure (RingHom.ker (algebraMap A (Localization.Away d))) ↦
        (p : A ⧸ D.deltaClosure (RingHom.ker (algebraMap A (Localization.Away d)))) * x) := by
  subst d
  exact D.p_mul_injective_torsionReduction

end SerrePositivity.BhattScholze.DeltaStructure

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- p除算添加後の既存旧ねじれ除去商はp正則。完備化前の具体的候補。 -/
theorem deltaDivisionTorsionQuotient_p_mul_injective
    (D : DeltaStructure p A) (a : σ → A) :
    Function.Injective (fun x : DeltaDivisionTorsionQuotient D (p : A) a ↦
      (p : DeltaDivisionTorsionQuotient D (p : A) a) * x) := by
  exact (deltaAdjoinDivisionStructure D (p : A) a).p_mul_injective_torsionReduction_of_eq_p
    (deltaAdjoinDivisionMap D (p : A) a (p : A)) (map_natCast _ _)

end SerrePositivity.BhattScholze

end DeltaPTorsionReduction

/-! ## δ除算商の古典的(p,d)完備化

BS 著者版 Proposition 7.2の代数的商に古典的完備化を適用する具体的な工程。
導来完備化との比較、新dねじれの不存在、prismの存在は主張しない。
-/

@[expose] public noncomputable section DeltaDivisionClassicalCompletion

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 二段階δ除算商内の(p,d)イデアル。 -/
def deltaDivisionAdicIdeal (D : DeltaStructure p R) (d : R) (a : σ → R) :
    Ideal (DeltaDivisionTorsionQuotient D d a) :=
  Ideal.span {(p : DeltaDivisionTorsionQuotient D d a), deltaDivisionTorsionMap D d a d}

/-- 二段階δ除算商の古典的(p,d)完備化。 -/
abbrev ClassicalDeltaDivisionCompletion (D : DeltaStructure p R) (d : R) (a : σ → R) :=
  AdicCompletion (deltaDivisionAdicIdeal D d a) (DeltaDivisionTorsionQuotient D d a)

/-- (p,d)イデアルは有限生成。 -/
theorem deltaDivisionAdicIdeal_fg (D : DeltaStructure p R) (d : R) (a : σ → R) :
    (deltaDivisionAdicIdeal D d a).FG :=
  Submodule.fg_span (Set.toFinite _)

/-- 古典的(p,d)完備化のδ構造。 -/
def classicalDeltaDivisionStructure (D : DeltaStructure p R) (d : R) (a : σ → R) :
    DeltaStructure p (ClassicalDeltaDivisionCompletion D d a) :=
  (deltaDivisionTorsionStructure D d a).adicCompletion (deltaDivisionAdicIdeal D d a)
    (Ideal.subset_span (by simp))

/-- 基底から古典的(p,d)完備化への標準射。 -/
def classicalDeltaDivisionMap (D : DeltaStructure p R) (d : R) (a : σ → R) :
    R →+* ClassicalDeltaDivisionCompletion D d a :=
  (algebraMap (DeltaDivisionTorsionQuotient D d a) _).comp (deltaDivisionTorsionMap D d a)

/-- 二段階δ除算商への標準射はδ射。 -/
theorem deltaDivisionTorsionMap_isDeltaHom (D : DeltaStructure p R) (d : R) (a : σ → R) :
    D.IsDeltaHom (deltaDivisionTorsionStructure D d a) (deltaDivisionTorsionMap D d a) :=
  ((deltaAdjoinDivisionStructure D d a).isDeltaHom_quotient_mk _
    ((deltaAdjoinDivisionStructure D d a).isStable_deltaClosure _)).comp
      (deltaAdjoinDivisionMap_isDeltaHom D d a)

/-- 古典的完備化への標準基底射はδ射。 -/
theorem classicalDeltaDivisionMap_isDeltaHom (D : DeltaStructure p R) (d : R) (a : σ → R) :
    D.IsDeltaHom (classicalDeltaDivisionStructure D d a) (classicalDeltaDivisionMap D d a) :=
  ((deltaDivisionTorsionStructure D d a).isDeltaHom_adicCompletion
    (deltaDivisionAdicIdeal D d a) (Ideal.subset_span (by simp))).comp
      (deltaDivisionTorsionMap_isDeltaHom D d a)

/-- f(d)が正則、全f(a_s)がf(d)で割り切れ、終域がp,f(d)を含むJで完備なら、
古典的完備化したδ除算商から基底射fを延長するδ射が一意に存在する。 -/
theorem existsUnique_classicalDeltaDivisionHom {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (E : DeltaStructure p A) (d : R) (a : σ → R)
    (f : R →+* A) (hf : D.IsDeltaHom E f)
    (hd : Function.Injective (fun x : A ↦ f d * x)) (ha : ∀ s, f d ∣ f (a s))
    (J : Ideal A) [IsAdicComplete J A] (hpJ : (p : A) ∈ J) (hdJ : f d ∈ J) :
    ∃! g : ClassicalDeltaDivisionCompletion D d a →+* A,
      (classicalDeltaDivisionStructure D d a).IsDeltaHom E g ∧
        g.comp (classicalDeltaDivisionMap D d a) = f := by
  let B := DeltaDivisionTorsionQuotient D d a
  let DB := deltaDivisionTorsionStructure D d a
  let j := deltaDivisionTorsionMap D d a
  let I := deltaDivisionAdicIdeal D d a
  let c := algebraMap B (AdicCompletion I B)
  have hc := DB.isDeltaHom_adicCompletion I (Ideal.subset_span (by simp))
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaDivisionTorsionHom D E d a f hf hd ha
  have hIJ : I.map k ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change k (p : B) ∈ J
      simpa only [map_natCast] using hpJ
    · have h := DFunLike.congr_fun hk.2 d
      change k (j d) = f d at h
      change k (j d) ∈ J
      simpa only [h] using hdJ
  obtain ⟨g, hg, hgu⟩ := DB.existsUnique_adicCompletion_lift E I
    (Ideal.subset_span (by simp))
    (deltaDivisionAdicIdeal_fg D d a) J k hk.1 hIJ
  refine ⟨g, ⟨hg.2, ?_⟩, ?_⟩
  · change g.comp (c.comp j) = f
    rw [← RingHom.comp_assoc, hg.1, hk.2]
  · intro l hl
    have hlk : l.comp c = k := by
      apply hku (l.comp c)
      refine ⟨hl.1.comp hc, ?_⟩
      change (l.comp c).comp j = f
      rw [RingHom.comp_assoc]
      exact hl.2
    apply hgu l
    exact ⟨hlk, hl.1⟩

end SerrePositivity.BhattScholze

end DeltaDivisionClassicalCompletion

/-! ## δ除算・旧ねじれ商・実導来(p,d)完備化の一段操作

BS 著者版 Proposition 7.2の一段を、F3の実Koszul H⁰と証明済みδ延長に接続する。
完備化後の新dねじれの不存在やprismの存在は結論しない。
-/

@[expose] public noncomputable section DeltaDivisionPDCompletion

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type u}

/-- 旧ねじれδ閉包商に実導来(p,d)完備化H⁰を施した具体的な候補。 -/
abbrev DerivedDeltaDivisionCompletion (D : DeltaStructure p R) (d : R) (a : σ → R) :=
  PDCompletionH0 (DeltaDivisionTorsionQuotient D d a) p (deltaDivisionTorsionMap D d a d)

/-- 候補の環構造はF3の実H⁰の環構造。 -/
@[instance_reducible] def derivedDeltaDivisionCommRing
    (D : DeltaStructure p R) (d : R) (a : σ → R) :
    CommRing (DerivedDeltaDivisionCompletion D d a) :=
  pdCompletionCommRing (DeltaDivisionTorsionQuotient D d a) p (deltaDivisionTorsionMap D d a d)

/-- 候補のδ構造は実導来完備化への一意延長。 -/
def derivedDeltaDivisionStructure (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    DeltaStructure p (DerivedDeltaDivisionCompletion D d a) :=
  deltaPDCompletionStructure (deltaDivisionTorsionStructure D d a) (deltaDivisionTorsionMap D d a d)

/-- 元の環から一段候補への具体的な標準射。 -/
def derivedDeltaDivisionMap (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    R →+* DerivedDeltaDivisionCompletion D d a :=
  (pdCompletionUnit (DeltaDivisionTorsionQuotient D d a) p (deltaDivisionTorsionMap D d a d)).comp
    (deltaDivisionTorsionMap D d a)

/-- 標準射はδ射。 -/
theorem derivedDeltaDivisionMap_isDeltaHom (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    D.IsDeltaHom (derivedDeltaDivisionStructure D d a) (derivedDeltaDivisionMap D d a) := by
  let := derivedDeltaDivisionCommRing D d a
  exact (pdCompletionUnit_isDeltaHom (deltaDivisionTorsionStructure D d a)
    (deltaDivisionTorsionMap D d a d)).comp (deltaDivisionTorsionMap_isDeltaHom D d a)

/-- 一段候補は自身の作用について実p導来完備。 -/
theorem derivedDeltaDivision_complete_p (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    IsModuleComplete (DerivedDeltaDivisionCompletion D d a)
      (p : DerivedDeltaDivisionCompletion D d a)
      (ModuleCat.of (DerivedDeltaDivisionCompletion D d a)
        (DerivedDeltaDivisionCompletion D d a)) :=
  pdCompletionH0_self_complete_p (DeltaDivisionTorsionQuotient D d a) p
    (deltaDivisionTorsionMap D d a d)

/-- 一段候補は自身の作用についてdの標準像に実導来完備。 -/
theorem derivedDeltaDivision_complete_d (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    IsModuleComplete (DerivedDeltaDivisionCompletion D d a) (derivedDeltaDivisionMap D d a d)
      (ModuleCat.of (DerivedDeltaDivisionCompletion D d a)
        (DerivedDeltaDivisionCompletion D d a)) :=
  pdCompletionH0_self_complete_d (DeltaDivisionTorsionQuotient D d a) p
    (deltaDivisionTorsionMap D d a d)

/-- dがdistinguishedなら、一段候補での像もdistinguished。正則性とは区別する。 -/
theorem derivedDeltaDivisionMap_isDistinguished (D : DeltaStructure p R) (d : R) (a : σ → R)
    (hd : D.IsDistinguished d) :
    letI := derivedDeltaDivisionCommRing D d a
    (derivedDeltaDivisionStructure D d a).IsDistinguished (derivedDeltaDivisionMap D d a d) := by
  let := derivedDeltaDivisionCommRing D d a
  exact (derivedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd

/-- 各添加元の標準像は、一段候補のd像で割り切れる。 -/
theorem derivedDeltaDivisionMap_dvd (D : DeltaStructure p R) (d : R) (a : σ → R) (s : σ) :
    letI := derivedDeltaDivisionCommRing D d a
    derivedDeltaDivisionMap D d a d ∣ derivedDeltaDivisionMap D d a (a s) := by
  let := derivedDeltaDivisionCommRing D d a
  let U := DeltaDivisionTorsionQuotient D d a
  let c := pdCompletionUnit U p (deltaDivisionTorsionMap D d a d)
  let h : DeltaAdjoinDivision D d a →+* DerivedDeltaDivisionCompletion D d a :=
    c.comp (Ideal.Quotient.mk _)
  have he := congrArg h (deltaAdjoinDivision_relation D d a s)
  rw [map_mul] at he
  exact ⟨h (deltaAdjoinDivisionVariable D d a s), he.symm⟩

/-- 元族が生成する任意のイデアルは、一段候補のd像の主イデアルへ入る。 -/
theorem derivedDeltaDivisionMap_spanned_ideal_le (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    Ideal.span (Set.range a) ≤ (Ideal.span {derivedDeltaDivisionMap D d a d}).comap
      (derivedDeltaDivisionMap D d a) := by
  let := derivedDeltaDivisionCommRing D d a
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  exact Ideal.mem_span_singleton.mpr (derivedDeltaDivisionMap_dvd D d a s)

/-- 正則なd像と可除性を持つδ基底射は、実一段候補から一意に延長する。
試験環のp,f(d)実導来完備性を明示し、一般のpねじれを許す。 -/
theorem existsUnique_derivedDeltaDivisionHom {T : Type u} [CommRing T]
    (D : DeltaStructure p R) (E : DeltaStructure p T) (d : R) (a : σ → R)
    (f : R →+* T) (hf : D.IsDeltaHom E f)
    (hreg : Function.Injective (fun x : T ↦ f d * x)) (ha : ∀ s, f d ∣ f (a s))
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (f d) (ModuleCat.of T T)) :
    letI := derivedDeltaDivisionCommRing D d a
    ∃! h : DerivedDeltaDivisionCompletion D d a →+* T,
      (derivedDeltaDivisionStructure D d a).IsDeltaHom E h ∧
        h.comp (derivedDeltaDivisionMap D d a) = f := by
  let := derivedDeltaDivisionCommRing D d a
  let U := DeltaDivisionTorsionQuotient D d a
  let DU := deltaDivisionTorsionStructure D d a
  let j := deltaDivisionTorsionMap D d a
  let c := pdCompletionUnit U p (j d)
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaDivisionTorsionHom D E d a f hf hreg ha
  have hkd : k (j d) = f d := RingHom.congr_fun hk.2 d
  have hd' : IsModuleComplete T (k (j d)) (ModuleCat.of T T) := by rw [hkd]; exact hd
  obtain ⟨h, hh, hu⟩ := existsUnique_deltaPDCompletionHom DU (j d) E k hk.1 hp hd'
  refine ⟨h, ⟨hh.1, ?_⟩, ?_⟩
  · change h.comp (c.comp j) = f
    rw [← RingHom.comp_assoc, hh.2, hk.2]
  · intro l hl
    apply hu l
    refine ⟨hl.1, ?_⟩
    apply hku (l.comp c)
    refine ⟨hl.1.comp (pdCompletionUnit_isDeltaHom DU (j d)), ?_⟩
    change (l.comp c).comp j = f
    rw [RingHom.comp_assoc]
    exact hl.2

end SerrePositivity.BhattScholze

end DeltaDivisionPDCompletion

/-! ## 除算添加後のmod dへの商射

BS 著者版 Proposition 7.2のR→Δ/dがSを経由する代数的な計算。
Rの任意のイデアルJの全元をdで割る添加環と旧ねじれ除去商に対し、
R/Jからmod dへの標準環射を構成する。完備性は仮定せず、prismとは呼ばない。
-/

@[expose] public noncomputable section DeltaDivisionQuotient

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 除算添加・旧ねじれ除去の後も各a_sの像はdの像で割り切れる。 -/
theorem deltaDivisionTorsionMap_dvd {σ : Type*}
    (D : DeltaStructure p R) (d : R) (a : σ → R) (s : σ) :
    deltaDivisionTorsionMap D d a d ∣ deltaDivisionTorsionMap D d a (a s) := by
  let q : DeltaAdjoinDivision D d a →+* DeltaDivisionTorsionQuotient D d a :=
    Ideal.Quotient.mk _
  refine ⟨q (deltaAdjoinDivisionVariable D d a s), ?_⟩
  have h := congrArg q (deltaAdjoinDivision_relation D d a s)
  rw [map_mul] at h
  exact h.symm

/-- イデアルJの全元をdで割る二段階商で、Jの像はdの像の主イデアルに含まれる。 -/
theorem deltaDivisionTorsionMap_ideal_le_span (D : DeltaStructure p R) (d : R)
    (J : Ideal R) :
    J ≤ (Ideal.span {deltaDivisionTorsionMap D d (fun x : J ↦ (x : R)) d}).comap
      (deltaDivisionTorsionMap D d (fun x : J ↦ (x : R))) := by
  intro x hx
  change deltaDivisionTorsionMap D d (fun x : J ↦ (x : R)) x ∈
    Ideal.span {deltaDivisionTorsionMap D d (fun x : J ↦ (x : R)) d}
  apply Ideal.mem_span_singleton.mpr
  exact deltaDivisionTorsionMap_dvd D d (fun x : J ↦ (x : R)) ⟨x, hx⟩

/-- Jの全元をdで割った後、mod dへの基底射はR/Jを経由する。
任意の商Jを扱い、pねじれや導来・古典的完備性を追加仮定しない。 -/
def deltaDivisionQuotientMap (D : DeltaStructure p R) (d : R) (J : Ideal R) :
    R ⧸ J →+*
      (DeltaDivisionTorsionQuotient D d (fun x : J ↦ (x : R)) ⧸
        Ideal.span {deltaDivisionTorsionMap D d (fun x : J ↦ (x : R)) d}) :=
  Ideal.Quotient.lift J
    ((Ideal.Quotient.mk _).comp (deltaDivisionTorsionMap D d (fun x : J ↦ (x : R))))
    (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact deltaDivisionTorsionMap_ideal_le_span D d J hx)

/-- R/Jからの標準射はRの代表元上で、二段階商への射とmod d商射の合成に一致する。 -/
@[simp] theorem deltaDivisionQuotientMap_mk (D : DeltaStructure p R) (d : R)
    (J : Ideal R) (x : R) :
    deltaDivisionQuotientMap D d J (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk _ (deltaDivisionTorsionMap D d (fun x : J ↦ (x : R)) x) := rfl

end SerrePositivity.BhattScholze

end DeltaDivisionQuotient
