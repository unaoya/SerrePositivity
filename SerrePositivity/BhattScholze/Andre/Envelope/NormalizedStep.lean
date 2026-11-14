module

public import SerrePositivity.BhattScholze.Andre.Envelope.Normalized
public import SerrePositivity.BhattScholze.Andre.Envelope.RootRelation
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteDelta
public import SerrePositivity.HomologicalAlgebra.TorFlatBaseChangeVanishing

/-!
# 正規化 δ 関係の一段の Koszul 分解

## 概要
一段での Koszul 分解と相対比較、前段関係だけで割った源商での最高段関係の正則性、全相対自由環の下位関係商との比較、最高段 Koszul 複体から次段の正規化商への擬同型と Tor の消滅。
BS 著者版 Remark 7.15 の包の比較に使う、正規化した δ 関係の一段での Koszul 分解を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/JetKoszul`。
-/

universe u

/-! ## 有限正規化δ関係の一段におけるKoszul分解と相対比較

既存の正規化関係を最高変数分離・前段商への係数変更で実根関係へ移す。
δ包との比較の追加仮定や、完備化後の完全忠実平坦性は別の工程。
-/

@[expose] public noncomputable section DeltaDivisionNormalizedStepKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)

/-- 最高変数を分離し、下位係数を前段の実正規化商へ送る標準射。 -/
def Andre.deltaDivisionNormalizedStepPolynomialMap :
    MvPolynomial (σ × Fin (N + 2)) A →+*
      MvPolynomial σ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v N) :=
  (MvPolynomial.map (Ideal.Quotient.mk
    (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a v N))).comp
    (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom

/-- 下位多項式の標準包含は前段商の係数像へ移る。 -/
theorem Andre.deltaDivisionNormalizedStepPolynomialMap_inclusion
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepPolynomialMap D d a v N
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteStepInclusion N σ f) =
      MvPolynomial.C (Ideal.Quotient.mk _ f) := by
  change MvPolynomial.map _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
    (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteStepInclusion N σ f)) = _
  rw [_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion, MvPolynomial.map_C]

/-- 最高段変数は実際の新しい根変数に対応する。 -/
theorem Andre.deltaDivisionNormalizedStepPolynomialMap_top (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepPolynomialMap D d a v N
      (MvPolynomial.X (s, Fin.last (N + 1))) = MvPolynomial.X s := by
  change MvPolynomial.map _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
    (MvPolynomial.X (s, Fin.last (N + 1)))) = _
  rw [_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv_X_top, MvPolynomial.map_X]

/-- 実正規化関係式の標準像は、前段商の指定係数のp乗根関係そのもの。 -/
theorem Andre.deltaDivisionNormalizedStepPolynomialMap_relation (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepPolynomialMap D d a v N
      (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a v N) s := by
  change MvPolynomial.map _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
    (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N)) = _
  rw [_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial_top_split, map_sub, map_pow,
    MvPolynomial.map_X, MvPolynomial.map_C]
  rfl

/-- 異なる有限個の最高段関係の実像は、前段商上の弱正則列。 -/
theorem Andre.deltaDivisionNormalizedStepRelation_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial σ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v N))
      (List.ofFn fun i ↦ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepPolynomialMap D d a v N
        (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) := by
  simpa only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepPolynomialMap_relation] using
    _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelation_fin_isWeaklyRegular (p := p)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a v N) s hs

/-- 同じ実関係像の有限Koszul複体は、その実通常商の分解となる。 -/
theorem Andre.deltaDivisionNormalizedStepRelation_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i ↦ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepPolynomialMap D d a v N
      (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepRelation_fin_isWeaklyRegular D d a v N s hs

/-- 前段商の任意係数加群と任意有限係数列を伴う実相対添加写像は擬同型。 -/
theorem Andre.deltaDivisionNormalizedStepRelativeKoszulAugmentation_quasiIso {m k : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s)
    (M : Type u) [AddCommGroup M] [Module (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v N) M]
    (c : Fin k → _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v N) :
    QuasiIso (_root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteRelativeKoszulAugmentation (p := p)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a v N) s hs M c) :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteRelativeKoszulAugmentation_quasiIso _ s hs M c

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedStepKoszul

/-! ## 前段関係だけで割った実源商と最高段関係の正則性 -/

@[expose] public noncomputable section DeltaDivisionNormalizedStepSourceQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)

/-- 次段源多項式環内の、前段表示イデアルの標準包含像。 -/
def Andre.deltaDivisionNormalizedStepSourceIdeal : Ideal (MvPolynomial (σ × Fin (N + 2)) A) :=
  (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a v N).map
    (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteStepInclusion N σ)

/-- 最高変数分離は前段関係の包含像を係数イデアルへ送る。 -/
theorem Andre.deltaDivisionNormalizedStepSourceIdeal_map_split :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N).map
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom =
    (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a v N).map
      (MvPolynomial.C : MvPolynomial (σ × Fin (N + 1)) A →+*
        MvPolynomial σ (MvPolynomial (σ × Fin (N + 1)) A)) := by
  unfold _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact _root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion N σ A f

/-- 前段関係だけで割った実源商は、前段実商上の最高変数の多項式環。 -/
def Andre.deltaDivisionNormalizedStepSourceQuotientEquiv :
    (MvPolynomial (σ × Fin (N + 2)) A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N) ≃+*
      MvPolynomial σ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v N) :=
  (Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingEquiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal_map_split D d a v N).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ)
      (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a v N)).symm.toRingEquiv

/-- 実源商の同型は、前工程の具体的標準射と一致する。 -/
theorem Andre.deltaDivisionNormalizedStepSourceQuotientEquiv_mk
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N (Ideal.Quotient.mk _ f) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepPolynomialMap D d a v N f := by
  change MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Ideal.Quotient.mk _)) MvPolynomial.X
    (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A f) =
    MvPolynomial.map (Ideal.Quotient.mk _) (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A f)
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 前段関係だけで割った実源商内でも、有限個の最高段関係は弱正則列。 -/
theorem Andre.deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (σ × Fin (N + 2)) A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
      (List.ofFn fun i ↦ Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) := by
  let e := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N
  let rs := List.ofFn fun i ↦ Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v (s i) N)
  refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map e) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  · simpa only [rs, List.map_ofFn, Function.comp_def, e,
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv_mk] using
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepRelation_fin_isWeaklyRegular D d a v N s hs

/-- 実源商内の最高段関係のKoszul複体は、対応する実通常商の分解。 -/
theorem Andre.deltaDivisionNormalizedStepSourceRelation_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i ↦
      Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular D d a v N s hs)

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedStepSourceQuotient

/-! ## 全相対自由環の下位正規化関係商と有限実源商の比較 -/

@[expose] public noncomputable section DeltaDivisionNormalizedAmbientSource

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)
local notation "J" => deltaDivisionFirstResidueIdeal D d a ⊔
  deltaDivisionFiniteNormalizedWittIdeal D d a v N
local notation "S₀" => MvPolynomial (σ × Fin (N + 2)) A ⧸
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 有限実源商の表示イデアルの初期包含像は、全自由環の下位正規化イデアル。 -/
theorem Andre.deltaDivisionNormalizedStepSourceIdeal_map_initial (hv : (v : A) = D.delta d) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N).map
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 2) σ A).toRingHom = J := by
  unfold _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal
  rw [Ideal.map_map, _root_.SerrePositivity.BhattScholze.relativeFreeFiniteStepInclusion_comp_initial]
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal_map_initial D d a v hv N

/-- 全自由環の下位正規化イデアルは、後続変数分離で係数イデアルへ移る。 -/
theorem Andre.deltaDivisionNormalizedAmbientSourceIdeal_map_split (hv : (v : A) = D.delta d) :
    Ideal.map (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A).toRingHom J =
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N).map
        (MvPolynomial.C : MvPolynomial (σ × Fin (N + 2)) A →+*
          MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin (N + 2)) A)) := by
  rw [← _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal_map_initial D d a v N hv, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact _root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv_initial (N + 2) σ A f

/-- 全自由環の下位正規化関係商は、有限実源商上の後続多項式環。 -/
def Andre.deltaDivisionNormalizedAmbientSourceEquiv (hv : (v : A) = D.delta d) :
    (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ ⧸ J) ≃+* MvPolynomial (σ × ℕ) S₀ :=
  (Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A).toRingEquiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceIdeal_map_split D d a v N hv).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)).symm.toRingEquiv

/-- 比較同型は全自由環の標準商射上で、分離後の係数商写像と一致する。 -/
theorem Andre.deltaDivisionNormalizedAmbientSourceEquiv_mk (hv : (v : A) = D.delta d)
    (f : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N))
        (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f) := by
  change MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)))
    MvPolynomial.X (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f) =
    MvPolynomial.map (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N))
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f)
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 初期有限多項式の商像は、有限実源商の標準係数像に一致する。 -/
theorem Andre.deltaDivisionNormalizedAmbientSourceEquiv_initial (hv : (v : A) = D.delta d)
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv
      (Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 2) σ A f)) =
      MvPolynomial.C (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N) f) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv_mk,
    _root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv_initial, MvPolynomial.map_C]

/-- 全自由環の下位正規化関係商でも、次のモニック関係の初期包含像は非零因子。 -/
theorem Andre.deltaDivisionNormalizedAmbientSource_relation_isSMulRegular
    (hv : (v : A) = D.delta d) (s : σ) :
    IsSMulRegular (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ ⧸ J)
      (Ideal.Quotient.mk J (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
        (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N))) := by
  have hr : IsSMulRegular S₀
      (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N)) := by
    have h := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular
      D d a v N (fun _ : Fin 1 ↦ s) (fun _ _ _ ↦ Subsingleton.elim _ _)
    simpa only [List.ofFn_const, List.replicate_one,
      RingTheory.Sequence.isWeaklyRegular_singleton_iff] using h
  let e := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv
  have he := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv_initial D d a v N hv
    (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N)
  change e (Ideal.Quotient.mk J (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
    (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N))) = _ at he
  intro f g hfg
  apply e.injective
  apply MvPolynomial.ext
  intro k
  apply hr
  have h := congrArg (fun z ↦ (e z).coeff k) hfg
  simpa only [smul_eq_mul, map_mul, he, MvPolynomial.coeff_C_mul] using h

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedAmbientSource

/-! ## 最高段関係を課した二重商と次段実正規化商の比較 -/

@[expose] public noncomputable section DeltaDivisionNormalizedStepQuotientComparison

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)

/-- 前段関係の実源商内の最高段関係イデアル。 -/
def Andre.deltaDivisionNormalizedStepTopIdeal :
    Ideal (MvPolynomial (σ × Fin (N + 2)) A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N) :=
  (Ideal.span (Set.range fun s ↦ _root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N)).map
    (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N))

/-- 最高段イデアルは実源商内の関係式像のspan。 -/
theorem Andre.deltaDivisionNormalizedStepTopIdeal_eq_span :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepTopIdeal D d a v N =
      Ideal.span (Set.range fun s ↦
        Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
          (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N)) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepTopIdeal, Ideal.map_span, ← Set.range_comp']

/-- 前段包含像と最高段関係を合わせたイデアルは、既存の次段表示イデアル。 -/
theorem Andre.deltaDivisionNormalizedStepSourceIdeal_sup_top :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N ⊔
      Ideal.span (Set.range fun s ↦ _root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N) =
      _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a v (N + 1) :=
  (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal_succ D d a v N).symm

/-- 実源商に最高段関係を課した二重商は、既存の次段実正規化商。 -/
def Andre.deltaDivisionNormalizedStepDoubleQuotientEquiv :
    ((MvPolynomial (σ × Fin (N + 2)) A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N) ⧸
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepTopIdeal D d a v N) ≃+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) :=
  (DoubleQuot.quotQuotEquivQuotSup (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (Ideal.span (Set.range fun s ↦ _root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N))).trans
    (Ideal.quotEquivOfEq (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal_sup_top D d a v N))

/-- 比較同型は元の多項式の二重商像を次段の標準商像へ送る。 -/
theorem Andre.deltaDivisionNormalizedStepDoubleQuotientEquiv_mk
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepDoubleQuotientEquiv D d a v N
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ f)) = Ideal.Quotient.mk _ f := by
  change Ideal.quotEquivOfEq (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal_sup_top D d a v N)
    (DoubleQuot.quotQuotEquivQuotSup _ _
    (DoubleQuot.quotQuotMk _ _ f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk]
  rfl

/-- 有限添字の場合、最高段全関係の列は実源商上のKoszul分解を与える。 -/
theorem Andre.deltaDivisionNormalizedStepAll_isKoszulResolution [Fintype σ] :
    SerrePositivity.IsKoszulResolution (fun i : Fin (Fintype.card σ) ↦
      Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v ((Fintype.equivFin σ).symm i) N)) :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceRelation_fin_isKoszulResolution D d a v N
    (Fintype.equivFin σ).symm (Fintype.equivFin σ).symm.injective

/-- 有限列挙による全最高段関係のspanは、実際の最高段イデアル。 -/
theorem Andre.deltaDivisionNormalizedStepAll_span [Fintype σ] :
    Ideal.span (Set.range fun i : Fin (Fintype.card σ) ↦
      Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v ((Fintype.equivFin σ).symm i) N)) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepTopIdeal D d a v N := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepTopIdeal_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(Fintype.equivFin σ).symm i, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨Fintype.equivFin σ s, ?_⟩
    simp only [Equiv.symm_apply_apply]

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedStepQuotientComparison

/-! ## 有限最高段Koszul複体から次段実正規化商への擬同型

有限性はこの途中の有限Koszulモデルだけに使用する。
-/

@[expose] public noncomputable section DeltaDivisionNormalizedStepResolution

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)
local notation "R₀" =>
  MvPolynomial (σ × Fin (N + 2)) A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 実源商から次段実正規化商への具体的標準射。 -/
def Andre.deltaDivisionNormalizedStepNextMap :
    R₀ →+* _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepDoubleQuotientEquiv D d a v N).toRingHom.comp
    (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepTopIdeal D d a v N))

/-- 源商からの標準射は、元の多項式上で次段の標準商射に一致する。 -/
theorem Andre.deltaDivisionNormalizedStepNextMap_mk
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap D d a v N (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ f :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepDoubleQuotientEquiv_mk D d a v N f

/-- 次段実商の標準実源商代数構造。 -/
@[instance_reducible] def Andre.deltaDivisionNormalizedStepNextAlgebra :
    Algebra R₀ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap D d a v N).toAlgebra

/-- 二重商比較は標準実源商代数同型。 -/
def Andre.deltaDivisionNormalizedStepDoubleQuotientAlgEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    (R₀ ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepTopIdeal D d a v N) ≃ₐ[R₀]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  apply AlgEquiv.ofRingEquiv (f := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepDoubleQuotientEquiv D d a v N)
  intro c
  rfl

variable [Fintype σ]
local notation "g" => fun i : Fin (Fintype.card σ) ↦
  Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (deltaDivisionWittNormalizedPolynomial D d a v (Equiv.symm (Fintype.equivFin σ) i) N)

/-- 有限全関係の実商は、次段実正規化商と標準実源商代数として同型。 -/
def Andre.deltaDivisionNormalizedStepAllQuotientAlgEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    (R₀ ⧸ Ideal.span (Set.range g)) ≃ₐ[R₀]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact (Ideal.quotientEquivAlgOfEq R₀ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepAll_span D d a v N)).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepDoubleQuotientAlgEquiv D d a v N)

/-- 最高段全関係Koszul複体の零次ホモロジーは、実際の次段正規化商。 -/
def Andre.deltaDivisionNormalizedStepHomologyZeroEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    (_root_.SerrePositivity.koszulComplex g).homology 0 ≃ₗ[R₀]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepAll_isKoszulResolution D d a v N).equiv.some.trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepAllQuotientAlgEquiv D d a v N).toLinearEquiv

/-- 有限最高段Koszul複体から次段実商の単一複体への具体的添加写像。 -/
def Andre.deltaDivisionNormalizedStepAugmentation :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    _root_.SerrePositivity.koszulComplex g ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of R₀ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1))) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact _root_.SerrePositivity.toSingleOfHomology _ _root_.SerrePositivity.koszulComplex_d_zero_one
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso.hom

/-- 具体的な最高段Koszul添加写像は次段実正規化商への擬同型。 -/
theorem Andre.deltaDivisionNormalizedStepAugmentation_quasiIso :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    QuasiIso (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepAugmentation D d a v N) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact _root_.SerrePositivity.quasiIso_toSingleOfHomology _ _root_.SerrePositivity.koszulComplex_d_zero_one
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso.hom
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepAll_isKoszulResolution D d a v N).isZero

/-- 添加写像の零次ホモロジー射は、構成に用いた実次段商への同型に一致する。 -/
theorem Andre.deltaDivisionNormalizedStepAugmentation_homologyMap :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    HomologicalComplex.homologyMap (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepAugmentation D d a v N) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R₀ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)))).hom =
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso.hom := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact _root_.SerrePositivity.toSingleOfHomology_homologyMap _ _root_.SerrePositivity.koszulComplex_d_zero_one _

/-- 有限最高段Koszul複体は、実際の次段正規化商の共通APIによる射影分解。 -/
def Andre.deltaDivisionNormalizedStepResolution :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    _root_.SerrePositivity.IsResolutionOf (_root_.SerrePositivity.koszulComplex g)
      (ModuleCat.of R₀ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1))) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact
    { isZero_X := _root_.SerrePositivity.koszulComplex_isZero_X_of_pos g
      projective := _root_.SerrePositivity.koszulComplex_projective_X g
      isZero_homology := (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepAll_isKoszulResolution D d a v N).isZero
      homologyZeroIso := (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso }

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedStepResolution

/-! ## 実正規化一段の標準スカラー塔と係数拡大加群に対するTor消滅

この計算には添字集合の有限性は不要。
-/

@[expose] public noncomputable section DeltaDivisionNormalizedStepTor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)
local notation "Q₀" => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v N
local notation "Q₁" => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)
local notation "R₀" =>
  MvPolynomial (σ × Fin (N + 2)) A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 前段商から実源商への標準係数射。 -/
def Andre.deltaDivisionNormalizedStepSourceCoefficientMap : Q₀ →+* R₀ :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).symm.toRingHom.comp MvPolynomial.C

/-- 標準係数射は元の下位多項式の包含像と一致する。 -/
theorem Andre.deltaDivisionNormalizedStepSourceCoefficientMap_mk
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceCoefficientMap D d a v N (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteStepInclusion N σ f) := by
  apply (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).injective
  change (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N)
    ((_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).symm _) = _
  rw [RingEquiv.apply_symm_apply, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv_mk,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepPolynomialMap_inclusion]

/-- 実源商を経由する標準射は既存の標準一段射に一致する。 -/
theorem Andre.deltaDivisionNormalizedStepNextMap_comp_coefficient :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap D d a v N).comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceCoefficientMap D d a v N) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap D d a v N := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro f
  change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap D d a v N
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceCoefficientMap D d a v N (Ideal.Quotient.mk _ f)) =
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap D d a v N (Ideal.Quotient.mk _ f)
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceCoefficientMap_mk,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap_mk, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap_mk]

/-- 実源商の標準前段商代数構造。 -/
@[instance_reducible] def Andre.deltaDivisionNormalizedStepSourceAlgebra : Algebra Q₀ R₀ :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceCoefficientMap D d a v N).toAlgebra

/-- 実源商の多項式表示は標準前段商代数同型。 -/
def Andre.deltaDivisionNormalizedStepSourceAlgEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
    R₀ ≃ₐ[Q₀] MvPolynomial σ Q₀ := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
  apply AlgEquiv.ofRingEquiv (f := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N)
  intro c
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).apply_symm_apply _

/-- 実源商は標準前段商射により自由。 -/
theorem Andre.deltaDivisionNormalizedStepSource_moduleFree :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
    Module.Free Q₀ R₀ := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
  exact Module.Free.of_equiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgEquiv D d a v N).symm.toLinearEquiv

/-- 実源商は標準前段商射により平坦。 -/
theorem Andre.deltaDivisionNormalizedStepSource_moduleFlat :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
    Module.Flat Q₀ R₀ := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSource_moduleFree D d a v N
  infer_instance

/-- 前段商・実源商・次段商の標準射はスカラー塔を構成する。 -/
theorem Andre.deltaDivisionNormalizedStep_isScalarTower :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    IsScalarTower Q₀ R₀ Q₁ := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  exact IsScalarTower.of_algebraMap_eq'
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap_comp_coefficient D d a v N).symm

/-- 任意前段商加群の係数拡大に対し、実源商上の次段実商の高次Torは零。 -/
theorem Andre.deltaDivisionNormalizedStep_tor_subsingleton
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    Subsingleton (_root_.SerrePositivity.TorModule R₀ (i + 1) Q₁ (TensorProduct Q₀ R₀ M)) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSource_moduleFlat D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStep_isScalarTower D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStep_moduleFaithfullyFlat D d a v N
  exact _root_.SerrePositivity.torModule_baseChange_subsingleton Q₀ R₀ Q₁ M (i + 1)
    (_root_.SerrePositivity.torModule_subsingleton_of_flat Q₁ M i)

/-- 同じ実導来テンソルは次数零に集中する。 -/
theorem Andre.deltaDivisionNormalizedStep_derivedTensor_concentrated
    (M : Type u) [AddCommGroup M] [Module Q₀ M] :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    _root_.SerrePositivity.IsConcentratedInDegreeZero (_root_.SerrePositivity.derivedTensor R₀ Q₁ (TensorProduct Q₀ R₀ M)) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  rw [_root_.SerrePositivity.isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStep_tor_subsingleton D d a v N M i

variable [Fintype σ]
local notation "g" => fun i : Fin (Fintype.card σ) ↦
  Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (deltaDivisionWittNormalizedPolynomial D d a v (Equiv.symm (Fintype.equivFin σ) i) N)

/-- 有限最高段の実Koszulホモロジーと、実際の次段商のTorとの比較。 -/
def Andre.deltaDivisionNormalizedStepKoszulTorIso
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    ModuleCat.of R₀ (_root_.SerrePositivity.TorModule R₀ i Q₁ (TensorProduct Q₀ R₀ M)) ≅
      ((_root_.SerrePositivity.koszulModuleFunctor g).obj
        (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M))).homology (-(i : ℤ)) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  exact _root_.SerrePositivity.torModuleIsoCochainLeft (TensorProduct Q₀ R₀ M)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepResolution D d a v N) i ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (_root_.SerrePositivity.koszulTensorConeIso g (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M)))

/-- 任意前段商加群を係数拡大した実最高段Koszul複体の負次ホモロジーは零。 -/
theorem Andre.deltaDivisionNormalizedStepKoszulHomology_isZero
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    IsZero (((_root_.SerrePositivity.koszulModuleFunctor g).obj
      (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M))).homology (-((i + 1 : ℕ) : ℤ))) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStep_tor_subsingleton D d a v N M i
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepKoszulTorIso D d a v N M (i + 1)).symm

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedStepTor
