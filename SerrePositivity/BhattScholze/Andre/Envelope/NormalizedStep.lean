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
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)

/-- 最高変数を分離し、下位係数を前段の実正規化商へ送る標準射。 -/
def deltaDivisionNormalizedStepPolynomialMap :
    MvPolynomial (σ × Fin (N + 2)) A →+*
      MvPolynomial σ (DeltaDivisionFiniteNormalizedQuotient D d a v N) :=
  (MvPolynomial.map (Ideal.Quotient.mk
    (deltaDivisionFiniteNormalizedPresentationIdeal D d a v N))).comp
    (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom

/-- 下位多項式の標準包含は前段商の係数像へ移る。 -/
theorem deltaDivisionNormalizedStepPolynomialMap_inclusion
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    deltaDivisionNormalizedStepPolynomialMap D d a v N
      (relativeFreeFiniteStepInclusion N σ f) =
      MvPolynomial.C (Ideal.Quotient.mk _ f) := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
    (relativeFreeFiniteStepInclusion N σ f)) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion, MvPolynomial.map_C]

/-- 最高段変数は実際の新しい根変数に対応する。 -/
theorem deltaDivisionNormalizedStepPolynomialMap_top (s : σ) :
    deltaDivisionNormalizedStepPolynomialMap D d a v N
      (MvPolynomial.X (s, Fin.last (N + 1))) = MvPolynomial.X s := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
    (MvPolynomial.X (s, Fin.last (N + 1)))) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_X_top, MvPolynomial.map_X]

/-- 実正規化関係式の標準像は、前段商の指定係数のp乗根関係そのもの。 -/
theorem deltaDivisionNormalizedStepPolynomialMap_relation (s : σ) :
    deltaDivisionNormalizedStepPolynomialMap D d a v N
      (deltaDivisionWittNormalizedPolynomial D d a v s N) =
      deltaRootRelationFamily (p := p)
        (deltaDivisionFiniteNormalizedStepCoefficients D d a v N) s := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
    (deltaDivisionWittNormalizedPolynomial D d a v s N)) = _
  rw [deltaDivisionWittNormalizedPolynomial_top_split, map_sub, map_pow,
    MvPolynomial.map_X, MvPolynomial.map_C]
  rfl

/-- 異なる有限個の最高段関係の実像は、前段商上の弱正則列。 -/
theorem deltaDivisionNormalizedStepRelation_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial σ (DeltaDivisionFiniteNormalizedQuotient D d a v N))
      (List.ofFn fun i ↦ deltaDivisionNormalizedStepPolynomialMap D d a v N
        (deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) := by
  simpa only [deltaDivisionNormalizedStepPolynomialMap_relation] using
    deltaRootRelation_fin_isWeaklyRegular (p := p)
      (deltaDivisionFiniteNormalizedStepCoefficients D d a v N) s hs

/-- 同じ実関係像の有限Koszul複体は、その実通常商の分解となる。 -/
theorem deltaDivisionNormalizedStepRelation_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i ↦ deltaDivisionNormalizedStepPolynomialMap D d a v N
      (deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  exact deltaDivisionNormalizedStepRelation_fin_isWeaklyRegular D d a v N s hs

/-- 前段商の任意係数加群と任意有限係数列を伴う実相対添加写像は擬同型。 -/
theorem deltaDivisionNormalizedStepRelativeKoszulAugmentation_quasiIso {m k : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s)
    (M : Type u) [AddCommGroup M] [Module (DeltaDivisionFiniteNormalizedQuotient D d a v N) M]
    (c : Fin k → DeltaDivisionFiniteNormalizedQuotient D d a v N) :
    QuasiIso (deltaRootFiniteRelativeKoszulAugmentation (p := p)
      (deltaDivisionFiniteNormalizedStepCoefficients D d a v N) s hs M c) :=
  deltaRootFiniteRelativeKoszulAugmentation_quasiIso _ s hs M c

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedStepKoszul

/-! ## 前段関係だけで割った実源商と最高段関係の正則性 -/

@[expose] public noncomputable section DeltaDivisionNormalizedStepSourceQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)

/-- 次段源多項式環内の、前段表示イデアルの標準包含像。 -/
def deltaDivisionNormalizedStepSourceIdeal : Ideal (MvPolynomial (σ × Fin (N + 2)) A) :=
  (deltaDivisionFiniteNormalizedPresentationIdeal D d a v N).map
    (relativeFreeFiniteStepInclusion N σ)

/-- 最高変数分離は前段関係の包含像を係数イデアルへ送る。 -/
theorem deltaDivisionNormalizedStepSourceIdeal_map_split :
    (deltaDivisionNormalizedStepSourceIdeal D d a v N).map
      (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom =
    (deltaDivisionFiniteNormalizedPresentationIdeal D d a v N).map
      (MvPolynomial.C : MvPolynomial (σ × Fin (N + 1)) A →+*
        MvPolynomial σ (MvPolynomial (σ × Fin (N + 1)) A)) := by
  unfold deltaDivisionNormalizedStepSourceIdeal
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion N σ A f

/-- 前段関係だけで割った実源商は、前段実商上の最高変数の多項式環。 -/
def deltaDivisionNormalizedStepSourceQuotientEquiv :
    (MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N) ≃+*
      MvPolynomial σ (DeltaDivisionFiniteNormalizedQuotient D d a v N) :=
  (Ideal.quotientEquiv _ _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingEquiv
    (deltaDivisionNormalizedStepSourceIdeal_map_split D d a v N).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ)
      (deltaDivisionFiniteNormalizedPresentationIdeal D d a v N)).symm.toRingEquiv

/-- 実源商の同型は、前工程の具体的標準射と一致する。 -/
theorem deltaDivisionNormalizedStepSourceQuotientEquiv_mk
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N (Ideal.Quotient.mk _ f) =
      deltaDivisionNormalizedStepPolynomialMap D d a v N f := by
  change MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Ideal.Quotient.mk _)) MvPolynomial.X
    (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A f) =
    MvPolynomial.map (Ideal.Quotient.mk _) (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A f)
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 前段関係だけで割った実源商内でも、有限個の最高段関係は弱正則列。 -/
theorem deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N)
      (List.ofFn fun i ↦ Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) := by
  let e := deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N
  let rs := List.ofFn fun i ↦ Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (deltaDivisionWittNormalizedPolynomial D d a v (s i) N)
  refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map e) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  · simpa only [rs, List.map_ofFn, Function.comp_def, e,
      deltaDivisionNormalizedStepSourceQuotientEquiv_mk] using
      deltaDivisionNormalizedStepRelation_fin_isWeaklyRegular D d a v N s hs

/-- 実源商内の最高段関係のKoszul複体は、対応する実通常商の分解。 -/
theorem deltaDivisionNormalizedStepSourceRelation_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i ↦
      Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular D d a v N s hs)

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
  deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 有限実源商の表示イデアルの初期包含像は、全自由環の下位正規化イデアル。 -/
theorem deltaDivisionNormalizedStepSourceIdeal_map_initial (hv : (v : A) = D.delta d) :
    (deltaDivisionNormalizedStepSourceIdeal D d a v N).map
      (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A).toRingHom = J := by
  unfold deltaDivisionNormalizedStepSourceIdeal
  rw [Ideal.map_map, relativeFreeFiniteStepInclusion_comp_initial]
  exact deltaDivisionFiniteNormalizedPresentationIdeal_map_initial D d a v hv N

/-- 全自由環の下位正規化イデアルは、後続変数分離で係数イデアルへ移る。 -/
theorem deltaDivisionNormalizedAmbientSourceIdeal_map_split (hv : (v : A) = D.delta d) :
    Ideal.map (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A).toRingHom J =
      (deltaDivisionNormalizedStepSourceIdeal D d a v N).map
        (MvPolynomial.C : MvPolynomial (σ × Fin (N + 2)) A →+*
          MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin (N + 2)) A)) := by
  rw [← deltaDivisionNormalizedStepSourceIdeal_map_initial D d a v N hv, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact relativeFreeFiniteVariableSplitAlgEquiv_initial (N + 2) σ A f

/-- 全自由環の下位正規化関係商は、有限実源商上の後続多項式環。 -/
def deltaDivisionNormalizedAmbientSourceEquiv (hv : (v : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ J) ≃+* MvPolynomial (σ × ℕ) S₀ :=
  (Ideal.quotientEquiv _ _ (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A).toRingEquiv
    (deltaDivisionNormalizedAmbientSourceIdeal_map_split D d a v N hv).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ)
      (deltaDivisionNormalizedStepSourceIdeal D d a v N)).symm.toRingEquiv

/-- 比較同型は全自由環の標準商射上で、分離後の係数商写像と一致する。 -/
theorem deltaDivisionNormalizedAmbientSourceEquiv_mk (hv : (v : A) = D.delta d)
    (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N))
        (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f) := by
  change MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)))
    MvPolynomial.X (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f) =
    MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N))
      (relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f)
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 初期有限多項式の商像は、有限実源商の標準係数像に一致する。 -/
theorem deltaDivisionNormalizedAmbientSourceEquiv_initial (hv : (v : A) = D.delta d)
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv
      (Ideal.Quotient.mk _ (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A f)) =
      MvPolynomial.C (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N) f) := by
  rw [deltaDivisionNormalizedAmbientSourceEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_initial, MvPolynomial.map_C]

/-- 全自由環の下位正規化関係商でも、次のモニック関係の初期包含像は非零因子。 -/
theorem deltaDivisionNormalizedAmbientSource_relation_isSMulRegular
    (hv : (v : A) = D.delta d) (s : σ) :
    IsSMulRegular (RelativeFreeDeltaRing (R := A) σ ⧸ J)
      (Ideal.Quotient.mk J (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a v s N))) := by
  have hr : IsSMulRegular S₀
      (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (deltaDivisionWittNormalizedPolynomial D d a v s N)) := by
    have h := deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular
      D d a v N (fun _ : Fin 1 ↦ s) (fun _ _ _ ↦ Subsingleton.elim _ _)
    simpa only [List.ofFn_const, List.replicate_one,
      RingTheory.Sequence.isWeaklyRegular_singleton_iff] using h
  let e := deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv
  have he := deltaDivisionNormalizedAmbientSourceEquiv_initial D d a v N hv
    (deltaDivisionWittNormalizedPolynomial D d a v s N)
  change e (Ideal.Quotient.mk J (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
    (deltaDivisionWittNormalizedPolynomial D d a v s N))) = _ at he
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
def deltaDivisionNormalizedStepTopIdeal :
    Ideal (MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N) :=
  (Ideal.span (Set.range fun s ↦ deltaDivisionWittNormalizedPolynomial D d a v s N)).map
    (Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N))

/-- 最高段イデアルは実源商内の関係式像のspan。 -/
theorem deltaDivisionNormalizedStepTopIdeal_eq_span :
    deltaDivisionNormalizedStepTopIdeal D d a v N =
      Ideal.span (Set.range fun s ↦
        Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
          (deltaDivisionWittNormalizedPolynomial D d a v s N)) := by
  rw [deltaDivisionNormalizedStepTopIdeal, Ideal.map_span, ← Set.range_comp']

/-- 前段包含像と最高段関係を合わせたイデアルは、既存の次段表示イデアル。 -/
theorem deltaDivisionNormalizedStepSourceIdeal_sup_top :
    deltaDivisionNormalizedStepSourceIdeal D d a v N ⊔
      Ideal.span (Set.range fun s ↦ deltaDivisionWittNormalizedPolynomial D d a v s N) =
      deltaDivisionFiniteNormalizedPresentationIdeal D d a v (N + 1) :=
  (deltaDivisionFiniteNormalizedPresentationIdeal_succ D d a v N).symm

/-- 実源商に最高段関係を課した二重商は、既存の次段実正規化商。 -/
def deltaDivisionNormalizedStepDoubleQuotientEquiv :
    ((MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N) ⧸
      deltaDivisionNormalizedStepTopIdeal D d a v N) ≃+*
      DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) :=
  (DoubleQuot.quotQuotEquivQuotSup (deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (Ideal.span (Set.range fun s ↦ deltaDivisionWittNormalizedPolynomial D d a v s N))).trans
    (Ideal.quotEquivOfEq (deltaDivisionNormalizedStepSourceIdeal_sup_top D d a v N))

/-- 比較同型は元の多項式の二重商像を次段の標準商像へ送る。 -/
theorem deltaDivisionNormalizedStepDoubleQuotientEquiv_mk
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    deltaDivisionNormalizedStepDoubleQuotientEquiv D d a v N
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ f)) = Ideal.Quotient.mk _ f := by
  change Ideal.quotEquivOfEq (deltaDivisionNormalizedStepSourceIdeal_sup_top D d a v N)
    (DoubleQuot.quotQuotEquivQuotSup _ _
    (DoubleQuot.quotQuotMk _ _ f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk]
  rfl

/-- 有限添字の場合、最高段全関係の列は実源商上のKoszul分解を与える。 -/
theorem deltaDivisionNormalizedStepAll_isKoszulResolution [Fintype σ] :
    SerrePositivity.IsKoszulResolution (fun i : Fin (Fintype.card σ) ↦
      Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (deltaDivisionWittNormalizedPolynomial D d a v ((Fintype.equivFin σ).symm i) N)) :=
  deltaDivisionNormalizedStepSourceRelation_fin_isKoszulResolution D d a v N
    (Fintype.equivFin σ).symm (Fintype.equivFin σ).symm.injective

/-- 有限列挙による全最高段関係のspanは、実際の最高段イデアル。 -/
theorem deltaDivisionNormalizedStepAll_span [Fintype σ] :
    Ideal.span (Set.range fun i : Fin (Fintype.card σ) ↦
      Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
        (deltaDivisionWittNormalizedPolynomial D d a v ((Fintype.equivFin σ).symm i) N)) =
      deltaDivisionNormalizedStepTopIdeal D d a v N := by
  rw [deltaDivisionNormalizedStepTopIdeal_eq_span]
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
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)
local notation "R₀" =>
  MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 実源商から次段実正規化商への具体的標準射。 -/
def deltaDivisionNormalizedStepNextMap :
    R₀ →+* DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) :=
  (deltaDivisionNormalizedStepDoubleQuotientEquiv D d a v N).toRingHom.comp
    (Ideal.Quotient.mk (deltaDivisionNormalizedStepTopIdeal D d a v N))

/-- 源商からの標準射は、元の多項式上で次段の標準商射に一致する。 -/
theorem deltaDivisionNormalizedStepNextMap_mk
    (f : MvPolynomial (σ × Fin (N + 2)) A) :
    deltaDivisionNormalizedStepNextMap D d a v N (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ f :=
  deltaDivisionNormalizedStepDoubleQuotientEquiv_mk D d a v N f

/-- 次段実商の標準実源商代数構造。 -/
@[instance_reducible] def deltaDivisionNormalizedStepNextAlgebra :
    Algebra R₀ (DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)) :=
  (deltaDivisionNormalizedStepNextMap D d a v N).toAlgebra

/-- 二重商比較は標準実源商代数同型。 -/
def deltaDivisionNormalizedStepDoubleQuotientAlgEquiv :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    (R₀ ⧸ deltaDivisionNormalizedStepTopIdeal D d a v N) ≃ₐ[R₀]
      DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) := by
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionNormalizedStepDoubleQuotientEquiv D d a v N)
  intro c
  rfl

variable [Fintype σ]
local notation "g" => fun i : Fin (Fintype.card σ) ↦
  Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (deltaDivisionWittNormalizedPolynomial D d a v (Equiv.symm (Fintype.equivFin σ) i) N)

/-- 有限全関係の実商は、次段実正規化商と標準実源商代数として同型。 -/
def deltaDivisionNormalizedStepAllQuotientAlgEquiv :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    (R₀ ⧸ Ideal.span (Set.range g)) ≃ₐ[R₀]
      DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) := by
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact (Ideal.quotientEquivAlgOfEq R₀ (deltaDivisionNormalizedStepAll_span D d a v N)).trans
    (deltaDivisionNormalizedStepDoubleQuotientAlgEquiv D d a v N)

/-- 最高段全関係Koszul複体の零次ホモロジーは、実際の次段正規化商。 -/
def deltaDivisionNormalizedStepHomologyZeroEquiv :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    (koszulComplex g).homology 0 ≃ₗ[R₀]
      DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1) := by
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact (deltaDivisionNormalizedStepAll_isKoszulResolution D d a v N).equiv.some.trans
    (deltaDivisionNormalizedStepAllQuotientAlgEquiv D d a v N).toLinearEquiv

/-- 有限最高段Koszul複体から次段実商の単一複体への具体的添加写像。 -/
def deltaDivisionNormalizedStepAugmentation :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    koszulComplex g ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of R₀ (DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1))) := by
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact toSingleOfHomology _ koszulComplex_d_zero_one
    (deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso.hom

/-- 具体的な最高段Koszul添加写像は次段実正規化商への擬同型。 -/
theorem deltaDivisionNormalizedStepAugmentation_quasiIso :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    QuasiIso (deltaDivisionNormalizedStepAugmentation D d a v N) := by
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact quasiIso_toSingleOfHomology _ koszulComplex_d_zero_one
    (deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso.hom
    (deltaDivisionNormalizedStepAll_isKoszulResolution D d a v N).isZero

/-- 添加写像の零次ホモロジー射は、構成に用いた実次段商への同型に一致する。 -/
theorem deltaDivisionNormalizedStepAugmentation_homologyMap :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    HomologicalComplex.homologyMap (deltaDivisionNormalizedStepAugmentation D d a v N) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of R₀ (DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)))).hom =
      (deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso.hom := by
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact toSingleOfHomology_homologyMap _ koszulComplex_d_zero_one _

/-- 有限最高段Koszul複体は、実際の次段正規化商の共通APIによる射影分解。 -/
def deltaDivisionNormalizedStepResolution :
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    IsResolutionOf (koszulComplex g)
      (ModuleCat.of R₀ (DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1))) := by
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  exact
    { isZero_X := koszulComplex_isZero_X_of_pos g
      projective := koszulComplex_projective_X g
      isZero_homology := (deltaDivisionNormalizedStepAll_isKoszulResolution D d a v N).isZero
      homologyZeroIso := (deltaDivisionNormalizedStepHomologyZeroEquiv D d a v N).toModuleIso }

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedStepResolution

/-! ## 実正規化一段の標準スカラー塔と係数拡大加群に対するTor消滅

この計算には添字集合の有限性は不要。
-/

@[expose] public noncomputable section DeltaDivisionNormalizedStepTor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)
local notation "Q₀" => DeltaDivisionFiniteNormalizedQuotient D d a v N
local notation "Q₁" => DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)
local notation "R₀" =>
  MvPolynomial (σ × Fin (N + 2)) A ⧸ deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 前段商から実源商への標準係数射。 -/
def deltaDivisionNormalizedStepSourceCoefficientMap : Q₀ →+* R₀ :=
  (deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).symm.toRingHom.comp MvPolynomial.C

/-- 標準係数射は元の下位多項式の包含像と一致する。 -/
theorem deltaDivisionNormalizedStepSourceCoefficientMap_mk
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    deltaDivisionNormalizedStepSourceCoefficientMap D d a v N (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (relativeFreeFiniteStepInclusion N σ f) := by
  apply (deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).injective
  change (deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N)
    ((deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaDivisionNormalizedStepSourceQuotientEquiv_mk,
    deltaDivisionNormalizedStepPolynomialMap_inclusion]

/-- 実源商を経由する標準射は既存の標準一段射に一致する。 -/
theorem deltaDivisionNormalizedStepNextMap_comp_coefficient :
    (deltaDivisionNormalizedStepNextMap D d a v N).comp
      (deltaDivisionNormalizedStepSourceCoefficientMap D d a v N) =
      deltaDivisionFiniteNormalizedStepMap D d a v N := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro f
  change deltaDivisionNormalizedStepNextMap D d a v N
    (deltaDivisionNormalizedStepSourceCoefficientMap D d a v N (Ideal.Quotient.mk _ f)) =
    deltaDivisionFiniteNormalizedStepMap D d a v N (Ideal.Quotient.mk _ f)
  rw [deltaDivisionNormalizedStepSourceCoefficientMap_mk,
    deltaDivisionNormalizedStepNextMap_mk, deltaDivisionFiniteNormalizedStepMap_mk]

/-- 実源商の標準前段商代数構造。 -/
@[instance_reducible] def deltaDivisionNormalizedStepSourceAlgebra : Algebra Q₀ R₀ :=
  (deltaDivisionNormalizedStepSourceCoefficientMap D d a v N).toAlgebra

/-- 実源商の多項式表示は標準前段商代数同型。 -/
def deltaDivisionNormalizedStepSourceAlgEquiv :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    R₀ ≃ₐ[Q₀] MvPolynomial σ Q₀ := by
  letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N)
  intro c
  exact (deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N).apply_symm_apply _

/-- 実源商は標準前段商射により自由。 -/
theorem deltaDivisionNormalizedStepSource_moduleFree :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    Module.Free Q₀ R₀ := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  exact Module.Free.of_equiv
    (deltaDivisionNormalizedStepSourceAlgEquiv D d a v N).symm.toLinearEquiv

/-- 実源商は標準前段商射により平坦。 -/
theorem deltaDivisionNormalizedStepSource_moduleFlat :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    Module.Flat Q₀ R₀ := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionNormalizedStepSource_moduleFree D d a v N
  infer_instance

/-- 前段商・実源商・次段商の標準射はスカラー塔を構成する。 -/
theorem deltaDivisionNormalizedStep_isScalarTower :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    IsScalarTower Q₀ R₀ Q₁ := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  exact IsScalarTower.of_algebraMap_eq'
    (deltaDivisionNormalizedStepNextMap_comp_coefficient D d a v N).symm

/-- 任意前段商加群の係数拡大に対し、実源商上の次段実商の高次Torは零。 -/
theorem deltaDivisionNormalizedStep_tor_subsingleton
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    Subsingleton (TorModule R₀ (i + 1) Q₁ (TensorProduct Q₀ R₀ M)) := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  let := deltaDivisionNormalizedStepSource_moduleFlat D d a v N
  let := deltaDivisionNormalizedStep_isScalarTower D d a v N
  let := deltaDivisionFiniteNormalizedStep_moduleFaithfullyFlat D d a v N
  exact torModule_baseChange_subsingleton Q₀ R₀ Q₁ M (i + 1)
    (torModule_subsingleton_of_flat Q₁ M i)

/-- 同じ実導来テンソルは次数零に集中する。 -/
theorem deltaDivisionNormalizedStep_derivedTensor_concentrated
    (M : Type u) [AddCommGroup M] [Module Q₀ M] :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    IsConcentratedInDegreeZero (derivedTensor R₀ Q₁ (TensorProduct Q₀ R₀ M)) := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact deltaDivisionNormalizedStep_tor_subsingleton D d a v N M i

variable [Fintype σ]
local notation "g" => fun i : Fin (Fintype.card σ) ↦
  Ideal.Quotient.mk (deltaDivisionNormalizedStepSourceIdeal D d a v N)
    (deltaDivisionWittNormalizedPolynomial D d a v (Equiv.symm (Fintype.equivFin σ) i) N)

/-- 有限最高段の実Koszulホモロジーと、実際の次段商のTorとの比較。 -/
def deltaDivisionNormalizedStepKoszulTorIso
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    ModuleCat.of R₀ (TorModule R₀ i Q₁ (TensorProduct Q₀ R₀ M)) ≅
      ((koszulModuleFunctor g).obj
        (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M))).homology (-(i : ℤ)) := by
  letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
  letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  exact torModuleIsoCochainLeft (TensorProduct Q₀ R₀ M)
    (deltaDivisionNormalizedStepResolution D d a v N) i ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (koszulTensorConeIso g (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M)))

/-- 任意前段商加群を係数拡大した実最高段Koszul複体の負次ホモロジーは零。 -/
theorem deltaDivisionNormalizedStepKoszulHomology_isZero
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := deltaDivisionNormalizedStepNextAlgebra D d a v N
    letI := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    IsZero (((koszulModuleFunctor g).obj
      (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M))).homology (-((i + 1 : ℕ) : ℤ))) := by
  let := deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := deltaDivisionNormalizedStepNextAlgebra D d a v N
  let := deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  let := deltaDivisionNormalizedStep_tor_subsingleton D d a v N M i
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (deltaDivisionNormalizedStepKoszulTorIso D d a v N M (i + 1)).symm

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedStepTor
