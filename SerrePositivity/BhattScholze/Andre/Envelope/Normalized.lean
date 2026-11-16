module

public import SerrePositivity.BhattScholze.Delta.Division.Witt
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Adjoin
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import SerrePositivity.BhattScholze.Delta.Division.Residue
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Colimit.Module
public import SerrePositivity.CommutativeAlgebra.DirectLimit
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# 正規化した δ 関係商の直極限と忠実平坦性

## 概要
有限正規化商の各段を前段商上のモニック冪根添加として実現し、段の射の自由性・忠実平坦性と直系を作る。その直極限を全段環として構成し、無限相対自由多項式環からの評価射の核が正規化関係イデアルであること、全 δ 剰余イデアルの Witt 正規化との比較、共通係数商上の平坦性・忠実平坦性を示す。
BS 著者版 Remark 7.15 の包の比較に使う、正規化した δ 関係商の直極限と忠実平坦性を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/DivisionResidue`、`Envelope/MonicSource`、`Envelope/NormalizedStep`。
-/

universe u v w

/-! ## 有限正規化商の一段を前段商上のモニック冪根添加として実現 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedPowerEquiv

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 既存の有限正規化表示イデアルによる通常商環。 -/
abbrev Andre.DeltaDivisionFiniteNormalizedQuotient (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) :=
  MvPolynomial (σ × Fin (N + 1)) A ⧸
    _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a u N

/-- 次段のモニック冪関係の係数は、具体的下位多項式の前段商像。 -/
def Andre.deltaDivisionFiniteNormalizedStepCoefficients (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) : σ → _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N :=
  fun s => Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedCoefficient D d a u s N)

/-- 次段有限正規化商は、前段商上の任意添字族モニック冪根添加環に同型。 -/
def Andre.deltaDivisionFiniteNormalizedStepPowerEquiv (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1) ≃+*
      _root_.SerrePositivity.BhattScholze.MonicPowerFamilyCover p σ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a u N) :=
  (Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingEquiv
    (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal_map_top_split D d a u N).symm).trans
    (_root_.SerrePositivity.BhattScholze.monicPowerFamilyBaseQuotientEquiv p σ (MvPolynomial (σ × Fin (N + 1)) A)
      (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a u N)
      (fun s => _root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedCoefficient D d a u s N))

/-- 次段商同型は前段の標準包含を根添加環の係数射に送る。 -/
theorem Andre.deltaDivisionFiniteNormalizedStepPowerEquiv_inclusion (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N
      (Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteStepInclusion N σ f)) =
      algebraMap (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
        (_root_.SerrePositivity.BhattScholze.MonicPowerFamilyCover p σ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
          (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a u N))
        (Ideal.Quotient.mk _ f) := by
  change _root_.SerrePositivity.BhattScholze.monicPowerFamilyBaseQuotientEquiv p σ (MvPolynomial (σ × Fin (N + 1)) A) _ _
    (Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteStepInclusion N σ f))) = _
  rw [_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion,
    _root_.SerrePositivity.BhattScholze.monicPowerFamilyBaseQuotientEquiv_C]
  rfl

/-- 次段商同型は最高変数を指定したp乗根に送る。 -/
theorem Andre.deltaDivisionFiniteNormalizedStepPowerEquiv_top (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N
      (Ideal.Quotient.mk _ (MvPolynomial.X (s, Fin.last (N + 1)))) =
      _root_.SerrePositivity.BhattScholze.monicPowerFamilyRoot p σ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a u N) s := by
  change _root_.SerrePositivity.BhattScholze.monicPowerFamilyBaseQuotientEquiv p σ (MvPolynomial (σ × Fin (N + 1)) A) _ _
    (Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
      (MvPolynomial.X (s, Fin.last (N + 1))))) = _
  rw [_root_.SerrePositivity.BhattScholze.relativeFreeFiniteTopVariableSplitAlgEquiv_X_top, _root_.SerrePositivity.BhattScholze.monicPowerFamilyBaseQuotientEquiv_X]
  rfl

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedPowerEquiv

/-! ## 有限正規化商の標準一段射の自由性と忠実平坦性 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedStepFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 前段商から次段商への係数射。標準包含との一致は次の公開定理で保証する。 -/
def Andre.deltaDivisionFiniteNormalizedStepMap (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N →+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N).symm.toRingHom.comp
    (algebraMap (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (_root_.SerrePositivity.BhattScholze.MonicPowerFamilyCover p σ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a u N)))

/-- 一段射は、有限多項式環の標準包含の商像と一致する。 -/
theorem Andre.deltaDivisionFiniteNormalizedStepMap_mk (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (N : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap D d a u N (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteStepInclusion N σ f) := by
  apply (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N).injective
  change (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N)
    ((_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N).symm _) = _
  rw [RingEquiv.apply_symm_apply, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerEquiv_inclusion]

/-- 標準一段射による前段商上の次段商の代数構造。 -/
@[instance_reducible] def Andre.deltaDivisionFiniteNormalizedStepAlgebra (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Algebra (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1)) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap D d a u N).toAlgebra

/-- 根添加表示は標準一段射についての前段商代数同型。 -/
def Andre.deltaDivisionFiniteNormalizedStepPowerAlgEquiv (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u N
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1) ≃ₐ[
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N]
      _root_.SerrePositivity.BhattScholze.MonicPowerFamilyCover p σ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a u N) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u N
  apply AlgEquiv.ofRingEquiv (f := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N)
  intro b
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerEquiv D d a u N).apply_symm_apply _

/-- 標準一段射の次段商は前段商上自由。 -/
theorem Andre.deltaDivisionFiniteNormalizedStep_moduleFree (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u N
    Module.Free (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1)) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u N
  let := _root_.SerrePositivity.BhattScholze.monicPowerFamilyCover_moduleFree p σ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a u N) (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerAlgEquiv D d a u N).symm.toLinearEquiv

/-- 標準一段射の次段商は前段商上平坦。 -/
theorem Andre.deltaDivisionFiniteNormalizedStep_moduleFlat (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u N
    Module.Flat (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1)) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStep_moduleFree D d a u N
  infer_instance

/-- 標準一段射は忠実平坦。前段商が零環の場合も含む。 -/
theorem Andre.deltaDivisionFiniteNormalizedStep_moduleFaithfullyFlat (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u N
    Module.FaithfullyFlat (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1)) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u N
  let := _root_.SerrePositivity.BhattScholze.monicPowerFamilyCover_moduleFaithfullyFlat_all p σ
    (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a u N) (Fact.out : p.Prime).pos
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepPowerAlgEquiv D d a u N).toLinearEquiv

/-- 標準一段射は単射であり、前段の関係を追加で消さない。 -/
theorem Andre.deltaDivisionFiniteNormalizedStepMap_injective (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Function.Injective (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap D d a u N) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStep_moduleFaithfullyFlat D d a u N
  exact FaithfulSMul.algebraMap_injective
    (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u (N + 1))

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedStepFlat

/-! ## 有限正規化商の標準射の直系 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedTowerMaps

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期有限多項式環の任意の後段への標準包含。 -/
def Andre.deltaDivisionFiniteNormalizedTowerInclusion (n m : ℕ) (h : n ≤ m) :
    MvPolynomial (σ × Fin (n + 1)) A →+* MvPolynomial (σ × Fin (m + 1)) A :=
  (MvPolynomial.rename fun z => (z.1, z.2.castLE (Nat.succ_le_succ h))).toRingHom

/-- 標準一段射を反復した、有限正規化商の任意の後段への射。 -/
def Andre.deltaDivisionFiniteNormalizedTowerMap (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u n →+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u m :=
  Nat.leRec (motive := fun m _ => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u n →+*
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u m)
    (RingHom.id _) (fun {k} _ f => (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap D d a u k).comp f) h

/-- 同じ有限段への標準射は恒等射。 -/
@[simp] theorem Andre.deltaDivisionFiniteNormalizedTowerMap_self (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.le_refl n) = RingHom.id _ := by
  simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap, Nat.leRec_self]

/-- 後段を一段進めた射は標準一段射との合成。 -/
theorem Andre.deltaDivisionFiniteNormalizedTowerMap_succ (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.le_succ_of_le h) =
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap D d a u m).comp
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h) := by
  simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap, Nat.leRec_succ _ _ h]

/-- 標準有限商射は任意三段の合成に整合する。 -/
theorem Andre.deltaDivisionFiniteNormalizedTowerMap_comp (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u hmk).comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u hnm) =
        _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.le_trans hnm hmk) := by
  induction hmk using Nat.leRec with
  | refl => rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_self, RingHom.id_comp]
  | le_succ_of_le h ih =>
      rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_succ D d a u h,
        _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_succ D d a u (Nat.le_trans hnm h),
        RingHom.comp_assoc, ih]

/-- 標準有限商射は全て単射。 -/
theorem Andre.deltaDivisionFiniteNormalizedTowerMap_injective (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    Function.Injective (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h) := by
  induction h using Nat.leRec with
  | refl => rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_self]; exact Function.injective_id
  | le_succ_of_le h ih =>
      rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_succ D d a u h]
      exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap_injective D d a u _).comp ih

/-- 任意後段への商射も、有限多項式環の標準rename包含に両立する。 -/
theorem Andre.deltaDivisionFiniteNormalizedTowerMap_mk (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m)
    (f : MvPolynomial (σ × Fin (n + 1)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerInclusion n m h f) := by
  induction h using Nat.leRec with
  | refl =>
      rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_self]
      change Ideal.Quotient.mk _ f = Ideal.Quotient.mk _ (MvPolynomial.rename _ f)
      congr 1
      change f = MvPolynomial.rename (fun z : σ × Fin (n + 1) => (z.1, z.2)) f
      exact (MvPolynomial.rename_id_apply f).symm
  | le_succ_of_le h ih =>
      rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_succ D d a u h, RingHom.comp_apply, ih,
        _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap_mk]
      congr 1
      unfold _root_.SerrePositivity.BhattScholze.relativeFreeFiniteStepInclusion _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerInclusion
      change MvPolynomial.rename _ (MvPolynomial.rename _ f) = MvPolynomial.rename _ f
      rw [MvPolynomial.rename_rename]
      rfl

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedTowerMaps

/-! ## 標準有限商直系の任意二段間の忠実平坦性 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedTowerFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 任意二段間の標準商射による代数構造。 -/
@[instance_reducible] def Andre.deltaDivisionFiniteNormalizedTowerAlgebra (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    Algebra (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u n)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u m) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h).toAlgebra

/-- 標準商射の合成は、後続一段についての係数塔の可換性を与える。 -/
theorem Andre.deltaDivisionFiniteNormalizedTower_scalarTower_succ (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u m
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u (Nat.le_succ_of_le h)
    IsScalarTower (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u n)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u m)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u (m + 1)) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u m
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u (Nat.le_succ_of_le h)
  apply IsScalarTower.of_algebraMap_eq
  intro b
  change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.le_succ_of_le h) b =
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap D d a u m
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h b)
  exact RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_succ D d a u h) b

/-- 任意二段間の標準有限商射は忠実平坦。零商を含む。 -/
theorem Andre.deltaDivisionFiniteNormalizedTower_moduleFaithfullyFlat (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
    Module.FaithfullyFlat (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u n)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u m) := by
  induction h using Nat.leRec with
  | refl =>
      simp +instances only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra,
        _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_self]
      infer_instance
  | @le_succ_of_le k h ih =>
      let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
      let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a u k
      let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u (Nat.le_succ_of_le h)
      let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTower_scalarTower_succ D d a u h
      let := ih
      let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStep_moduleFaithfullyFlat D d a u k
      exact Module.FaithfullyFlat.trans _ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u k) _

/-- 任意二段間の標準有限商射は平坦。 -/
theorem Andre.deltaDivisionFiniteNormalizedTower_moduleFlat (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
    Module.Flat (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u n)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u m) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTower_moduleFaithfullyFlat D d a u h
  infer_instance

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedTowerFlat

/-! ## 初期係数商と通常根添加環の比較射

A/(p,d,a_s)を明示し、初期多項式商と通常根添加環の具体的な同型を構成する。
さらに実際の初期δ剰余を後続変数の多項式環として表示する。
-/

@[expose] public noncomputable section DeltaDivisionFirstCoefficientPowerEquiv

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期剰余の基底係数イデアル。a_sの消滅を含む。 -/
def Andre.deltaDivisionFirstBaseIdeal (d : A) (a : σ → A) : Ideal A :=
  Ideal.span {(p : A), d} ⊔ Ideal.span (Set.range a)

/-- 初期根添加の係数族を適切な基底商へ送る。 -/
def Andre.deltaDivisionFirstPowerCoefficients (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) : σ → A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a :=
  fun s => Ideal.Quotient.mk _ ((u⁻¹ : Aˣ) * D.delta (a s))

/-- 適切な基底商上の初期通常根添加環。 -/
abbrev Andre.DeltaDivisionFirstPowerCover (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :=
  _root_.SerrePositivity.BhattScholze.MonicPowerFamilyCover p σ (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u)

/-- 初期多項式から、基底商上の具体的な根への評価射。 -/
def Andre.deltaDivisionFirstPowerEvaluation (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    MvPolynomial σ A →+* _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u :=
  MvPolynomial.eval₂Hom
    ((algebraMap (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u)).comp (Ideal.Quotient.mk _))
    (_root_.SerrePositivity.BhattScholze.monicPowerFamilyRoot p σ _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u))

/-- 根への評価射の係数上の式。 -/
@[simp] theorem Andre.deltaDivisionFirstPowerEvaluation_C
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerEvaluation D d a u (MvPolynomial.C r) =
      algebraMap (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u) (Ideal.Quotient.mk _ r) := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C r) = _
  rw [MvPolynomial.eval₂Hom_C]
  rfl

/-- 根への評価射の変数上の式。 -/
@[simp] theorem Andre.deltaDivisionFirstPowerEvaluation_X
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerEvaluation D d a u (MvPolynomial.X s) =
      _root_.SerrePositivity.BhattScholze.monicPowerFamilyRoot p σ _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u) s := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X s) = _
  rw [MvPolynomial.eval₂Hom_X']

/-- 初期係数イデアルは基底イデアルと指定モニック冪関係式の和。 -/
theorem Andre.deltaDivisionFirstPolynomialIdeal_eq_base_sup
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    _root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u =
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a).map
        (MvPolynomial.C : A →+* MvPolynomial σ A) ⊔
      _root_.SerrePositivity.BhattScholze.monicPowerFamilyRelationIdeal p σ A (fun s => (u⁻¹ : Aˣ) * D.delta (a s)) := by
  simp only [_root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal,
    _root_.SerrePositivity.BhattScholze.monicPowerFamilyRelationIdeal, Ideal.map_sup, Ideal.map_span,
    Set.image_pair, ← Set.range_comp', map_natCast]

/-- 従来の根評価射は、一般の係数商比較の標準商元上の射と一致する。 -/
theorem Andre.deltaDivisionFirstPowerEvaluation_eq_baseQuotient
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (x : MvPolynomial σ A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerEvaluation D d a u x =
      _root_.SerrePositivity.BhattScholze.monicPowerFamilyBaseQuotientEquiv p σ A
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a) (fun s => (u⁻¹ : Aˣ) * D.delta (a s))
        (Ideal.Quotient.mk _ x) := by
  rw [_root_.SerrePositivity.BhattScholze.monicPowerFamilyBaseQuotientEquiv_mk]
  change MvPolynomial.eval₂Hom _ _ x =
    MvPolynomial.eval₂Hom _ _ (MvPolynomial.map (Ideal.Quotient.mk _) x)
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl

/-- 初期根への評価射は、実際の初期係数多項式イデアルを消す。 -/
theorem Andre.deltaDivisionFirstPowerEvaluation_kills
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    ∀ x ∈ _root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u,
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerEvaluation D d a u x = 0 := by
  intro x hx
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialIdeal_eq_base_sup] at hx
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerEvaluation_eq_baseQuotient,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- 初期多項式商から適切な基底商上の通常根添加環への写像。 -/
def Andre.deltaDivisionFirstPolynomialToPowerCover
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    MvPolynomial σ A ⧸ _root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u →+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u :=
  Ideal.Quotient.lift _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerEvaluation D d a u)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerEvaluation_kills D d a u)

/-- 比較射は標準商射上で指定した評価射と一致する。 -/
theorem Andre.deltaDivisionFirstPolynomialToPowerCover_mk
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (x : MvPolynomial σ A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover D d a u
      (Ideal.Quotient.mk _ x) = _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerEvaluation D d a u x := rfl

/-- 比較射は元の係数を基底商の標準像へ送る。 -/
@[simp] theorem Andre.deltaDivisionFirstPolynomialToPowerCover_coeff
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover D d a u (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
      algebraMap (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u) (Ideal.Quotient.mk _ r) := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C r) = _
  rw [MvPolynomial.eval₂Hom_C]
  rfl

/-- 比較射は初期変数を通常根添加環の指定根へ送る。 -/
@[simp] theorem Andre.deltaDivisionFirstPolynomialToPowerCover_root
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover D d a u (Ideal.Quotient.mk _ (MvPolynomial.X s)) =
      _root_.SerrePositivity.BhattScholze.monicPowerFamilyRoot p σ _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u) s := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X s) = _
  rw [MvPolynomial.eval₂Hom_X']

/-- 従来の標準商射は、一般のモニック係数商表示によって全射。 -/
theorem Andre.deltaDivisionFirstPolynomialToPowerCover_surjective
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Function.Surjective (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover D d a u) := by
  let e := _root_.SerrePositivity.BhattScholze.monicPowerFamilyBaseQuotientEquiv p σ A
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a) (fun s => (u⁻¹ : Aˣ) * D.delta (a s))
  intro z
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm z)
  refine ⟨Ideal.Quotient.mk _ x, ?_⟩
  change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerEvaluation D d a u x = z
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerEvaluation_eq_baseQuotient]
  change e (Ideal.Quotient.mk _ x) = z
  rw [hx, e.apply_symm_apply]

/-- 基底係数イデアルの多項式環への像は初期関係式イデアルに含まれる。 -/
theorem Andre.deltaDivisionFirstBaseIdeal_map_C_le
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a).map
      (MvPolynomial.C : A →+* MvPolynomial σ A) ≤ _root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialIdeal_eq_base_sup]
  exact le_sup_left

/-- 適切な基底商から初期多項式商への標準係数射。 -/
def Andre.deltaDivisionFirstBaseToPolynomialQuotient
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a →+*
      MvPolynomial σ A ⧸ _root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u)).comp MvPolynomial.C)
    (fun _ hx => Ideal.Quotient.eq_zero_iff_mem.mpr
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal_map_C_le D d a u (Ideal.mem_map_of_mem _ hx)))

/-- 逆向き係数射は元の係数の標準像を保つ。 -/
@[simp] theorem Andre.deltaDivisionFirstBaseToPolynomialQuotient_mk
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseToPolynomialQuotient D d a u (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (MvPolynomial.C r) := rfl

/-- 初期多項式商の変数は基底商上の指定根である。 -/
theorem Andre.deltaDivisionFirstPolynomialQuotient_root_pow
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u) (MvPolynomial.X s)) ^ p =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseToPolynomialQuotient D d a u
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u s) := by
  have hm : Ideal.span (Set.range fun t => MvPolynomial.X t ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a t))) ≤
      _root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u := le_sup_right
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hm (Ideal.subset_span (Set.mem_range_self s)))
  rw [map_sub, map_pow, sub_eq_zero] at h
  exact h

/-- 指定根の普遍性による、通常根添加環から初期多項式商への逆向きの射。 -/
def Andre.deltaDivisionFirstPowerCoverToPolynomial
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u →+*
      MvPolynomial σ A ⧸ _root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u :=
  _root_.SerrePositivity.BhattScholze.monicPowerFamilyCoverMap p σ _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseToPolynomialQuotient D d a u)
    (fun s => Ideal.Quotient.mk _ (MvPolynomial.X s))
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialQuotient_root_pow D d a u)

/-- 逆向き比較射は元の係数を保つ。 -/
@[simp] theorem Andre.deltaDivisionFirstPowerCoverToPolynomial_coeff
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial D d a u
      (algebraMap (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u) (Ideal.Quotient.mk _ r)) =
      Ideal.Quotient.mk _ (MvPolynomial.C r) :=
  RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.monicPowerFamilyCoverMap_comp p σ _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseToPolynomialQuotient D d a u)
    (fun s => Ideal.Quotient.mk _ (MvPolynomial.X s))
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialQuotient_root_pow D d a u)) (Ideal.Quotient.mk _ r)

/-- 逆向き比較射は指定根を初期変数の剰余へ送る。 -/
@[simp] theorem Andre.deltaDivisionFirstPowerCoverToPolynomial_root
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial D d a u
      (_root_.SerrePositivity.BhattScholze.monicPowerFamilyRoot p σ _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u) s) =
      Ideal.Quotient.mk _ (MvPolynomial.X s) := _root_.SerrePositivity.BhattScholze.monicPowerFamilyCoverMap_root ..

/-- 初期多項式商上では比較射の往復が恒等射。 -/
theorem Andre.deltaDivisionFirstPowerCoverToPolynomial_comp_forward
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial D d a u).comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover D d a u) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial D d a u
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover D d a u
        (Ideal.Quotient.mk _ (MvPolynomial.C r))) = _
    rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover_coeff,
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial_coeff]
    rfl
  · intro s
    change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial D d a u
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover D d a u
        (Ideal.Quotient.mk _ (MvPolynomial.X s))) = _
    rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover_root,
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial_root]
    rfl

/-- 通常根添加環上でも比較射の往復が恒等射。 -/
theorem Andre.deltaDivisionFirstPolynomialToPowerCover_comp_backward
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover D d a u).comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial D d a u) = RingHom.id _ := by
  apply RingHom.ext
  intro y
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover_surjective D d a u y
  exact congrArg (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover D d a u)
    (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial_comp_forward D d a u) x)

/-- 初期係数多項式商は、A/(p,d,a_s)上の通常根添加環と同型。 -/
def Andre.deltaDivisionFirstCoefficientPowerEquiv
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (MvPolynomial σ A ⧸ _root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u) ≃+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u :=
  RingEquiv.ofRingHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover D d a u)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial D d a u)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover_comp_backward D d a u)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoverToPolynomial_comp_forward D d a u)

/-- 初期係数商の同型は元の係数の標準像を保つ。 -/
@[simp] theorem Andre.deltaDivisionFirstCoefficientPowerEquiv_coeff
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstCoefficientPowerEquiv D d a u (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
      algebraMap (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u) (Ideal.Quotient.mk _ r) :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover_coeff D d a u r

/-- 初期係数商の同型は初期変数を指定根へ送る。 -/
@[simp] theorem Andre.deltaDivisionFirstCoefficientPowerEquiv_root
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstCoefficientPowerEquiv D d a u (Ideal.Quotient.mk _ (MvPolynomial.X s)) =
      _root_.SerrePositivity.BhattScholze.monicPowerFamilyRoot p σ _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u) s :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPolynomialToPowerCover_root D d a u s

/-- 実際の初期δ剰余は、適切な基底商上の通常根添加環の後続多項式環。 -/
def Andre.deltaDivisionFirstResiduePowerPolynomialEquiv
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ ⧸ _root_.SerrePositivity.BhattScholze.deltaDivisionFirstResidueIdeal D d a) ≃+*
      MvPolynomial (σ × ℕ) (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u) :=
  (_root_.SerrePositivity.BhattScholze.deltaDivisionFirstResiduePolynomialEquiv D d a u hu).trans
    (MvPolynomial.mapEquiv (σ × ℕ) (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstCoefficientPowerEquiv D d a u))

/-- 初期δ剰余の指定根は、通常根添加環の指定根の係数像。 -/
@[simp] theorem Andre.deltaDivisionFirstResiduePowerPolynomialEquiv_initial
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.X (s, 0))) =
      MvPolynomial.C
        (_root_.SerrePositivity.BhattScholze.monicPowerFamilyRoot p σ _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u) s) := by
  change MvPolynomial.mapEquiv _ _
    (_root_.SerrePositivity.BhattScholze.deltaDivisionFirstResiduePolynomialEquiv D d a u hu _) = _
  rw [_root_.SerrePositivity.BhattScholze.deltaDivisionFirstResiduePolynomialEquiv_initial, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_C]
  exact congrArg MvPolynomial.C (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstCoefficientPowerEquiv_root D d a u s)

/-- 初期δ剰余の後続変数は通常根添加環上の自由変数。 -/
@[simp] theorem Andre.deltaDivisionFirstResiduePowerPolynomialEquiv_successor
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.X (s, n + 1))) =
      MvPolynomial.X (s, n) := by
  change MvPolynomial.mapEquiv _ _
    (_root_.SerrePositivity.BhattScholze.deltaDivisionFirstResiduePolynomialEquiv D d a u hu _) = _
  rw [_root_.SerrePositivity.BhattScholze.deltaDivisionFirstResiduePolynomialEquiv_successor, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_X]

end SerrePositivity.BhattScholze

end DeltaDivisionFirstCoefficientPowerEquiv

/-! ## 初期有限正規化商と適切な係数商上の根添加環の比較 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedInitialPowerEquiv

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 零段有限変数の唯一の段添字を除く標準多項式代数同型。 -/
def Andre.deltaDivisionFiniteNormalizedInitialVariableEquiv :
    MvPolynomial (σ × Fin 1) A ≃ₐ[A] MvPolynomial σ A :=
  MvPolynomial.renameEquiv A (Equiv.prodUnique σ (Fin 1))

/-- 零段有限イデアルは既存の第一係数多項式イデアルに移る。 -/
theorem Andre.deltaDivisionFiniteNormalizedPresentationIdeal_map_finOne (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    Ideal.map (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialVariableEquiv (σ := σ) (A := A)).toRingHom
      (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a u 0) =
      _root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal D d a u := by
  have hz : Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedGenerator D d a u 0)) = ⊥ := by
    apply le_bot_iff.mp
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    exact Fin.elim0 i
  unfold _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal
  rw [hz, sup_bot_eq]
  simp only [_root_.SerrePositivity.BhattScholze.deltaDivisionFirstPolynomialIdeal, Ideal.map_sup, Ideal.map_span,
    Set.image_pair, ← Set.range_comp']
  simp [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialVariableEquiv]

/-- 初期有限正規化商はA/(p,d,a_s)上の既存通常根添加環に同型。 -/
def Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0 ≃+* _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u :=
  (Ideal.quotientEquiv _ _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialVariableEquiv (σ := σ) (A := A)).toRingEquiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedPresentationIdeal_map_finOne D d a u).symm).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstCoefficientPowerEquiv D d a u)

/-- 初期商比較は基底係数の標準像を適切な係数商の係数射へ送る。 -/
theorem Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv_C (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (b : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u
      (Ideal.Quotient.mk _ (MvPolynomial.C b)) =
      algebraMap (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u) (Ideal.Quotient.mk _ b) := by
  change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstCoefficientPowerEquiv D d a u
    (Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialVariableEquiv (MvPolynomial.C b))) = _
  have hc : _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialVariableEquiv (σ := σ) (A := A)
      (MvPolynomial.C b) = MvPolynomial.C b := by
    simp [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialVariableEquiv]
  rw [hc, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstCoefficientPowerEquiv_coeff]

/-- 初期商比較は初期変数の標準商像を指定したp乗根へ送る。 -/
theorem Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv_X (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u
      (Ideal.Quotient.mk _ (MvPolynomial.X (s, (0 : Fin 1)))) =
      _root_.SerrePositivity.BhattScholze.monicPowerFamilyRoot p σ _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u) s := by
  change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstCoefficientPowerEquiv D d a u
    (Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialVariableEquiv
      (MvPolynomial.X (s, (0 : Fin 1))))) = _
  have hx : _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialVariableEquiv (σ := σ) (A := A)
      (MvPolynomial.X (s, (0 : Fin 1))) = MvPolynomial.X s := by
    simp [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialVariableEquiv]
  rw [hx, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstCoefficientPowerEquiv_root]

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedInitialPowerEquiv

/-! ## 適切な係数商上の初期有限正規化商の自由性と忠実平坦性 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedInitialFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- A/(p,d,a_s)から初期有限正規化商への具体的係数射。 -/
def Andre.deltaDivisionFiniteNormalizedInitialBaseMap (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a →+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0 :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u).symm.toRingHom.comp
    (algebraMap (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u))

/-- 初期係数射は元の基底係数の標準商像に一致する。 -/
theorem Andre.deltaDivisionFiniteNormalizedInitialBaseMap_mk (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (b : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseMap D d a u (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (MvPolynomial.C b) := by
  apply (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u).injective
  change (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u)
    ((_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u).symm _) = _
  rw [RingEquiv.apply_symm_apply, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv_C]

/-- 標準係数射による適切な係数商上の初期有限商の代数構造。 -/
@[instance_reducible] def Andre.deltaDivisionFiniteNormalizedInitialBaseAlgebra
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Algebra (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseMap D d a u).toAlgebra

/-- 初期根添加表示は標準係数射に関する代数同型。 -/
def Andre.deltaDivisionFiniteNormalizedInitialPowerAlgEquiv (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0 ≃ₐ[
      A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a] _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFirstPowerCover D d a u := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
  apply AlgEquiv.ofRingEquiv (f := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u)
  intro b
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerEquiv D d a u).apply_symm_apply _

/-- 初期有限正規化商はA/(p,d,a_s)上自由。 -/
theorem Andre.deltaDivisionFiniteNormalizedInitial_moduleFree (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
    Module.Free (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
  let := _root_.SerrePositivity.BhattScholze.monicPowerFamilyCover_moduleFree p σ
    (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u) (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerAlgEquiv D d a u).symm.toLinearEquiv

/-- 初期有限正規化商はA/(p,d,a_s)上平坦。 -/
theorem Andre.deltaDivisionFiniteNormalizedInitial_moduleFlat (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
    Module.Flat (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitial_moduleFree D d a u
  infer_instance

/-- 初期有限正規化商はA/(p,d,a_s)上忠実平坦。零係数商も含む。 -/
theorem Andre.deltaDivisionFiniteNormalizedInitial_moduleFaithfullyFlat (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
    Module.FaithfullyFlat (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
  let := _root_.SerrePositivity.BhattScholze.monicPowerFamilyCover_moduleFaithfullyFlat_all p σ
    (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstPowerCoefficients D d a u) (Fact.out : p.Prime).pos
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialPowerAlgEquiv D d a u).toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedInitialFlat

/-! ## 適切な共通係数商上の全有限正規化商の忠実平坦性 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedBaseFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- A/(p,d,a_s)から任意有限段への標準係数射。 -/
def Andre.deltaDivisionFiniteNormalizedBaseMap (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a →+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.zero_le N)).comp
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseMap D d a u)

/-- 任意有限段への係数射は、元の基底係数の標準商像に一致する。 -/
theorem Andre.deltaDivisionFiniteNormalizedBaseMap_mk (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) (b : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap D d a u N (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (MvPolynomial.C b) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap, RingHom.comp_apply,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseMap_mk, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_mk]
  congr 1
  simp [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerInclusion]

/-- 標準有限商射は適切な共通係数商からの係数射に両立する。 -/
theorem Andre.deltaDivisionFiniteNormalizedBaseMap_comp (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h).comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap D d a u n) =
        _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap D d a u m := by
  unfold _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap
  rw [← RingHom.comp_assoc, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_comp]

/-- 適切な共通係数商上の各有限正規化商の標準代数構造。 -/
@[instance_reducible] def Andre.deltaDivisionFiniteNormalizedBaseAlgebra (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Algebra (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap D d a u N).toAlgebra

/-- 全ての有限正規化商はA/(p,d,a_s)上忠実平坦。零係数商も含む。 -/
theorem Andre.deltaDivisionFiniteNormalized_moduleFaithfullyFlat (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
    Module.FaithfullyFlat (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseAlgebra D d a u
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u (Nat.zero_le N)
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  let : IsScalarTower (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitial_moduleFaithfullyFlat D d a u
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTower_moduleFaithfullyFlat D d a u (Nat.zero_le N)
  exact Module.FaithfullyFlat.trans _ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0) _

/-- 全ての有限正規化商はA/(p,d,a_s)上平坦。 -/
theorem Andre.deltaDivisionFiniteNormalized_moduleFlat (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
    Module.Flat (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalized_moduleFaithfullyFlat D d a u N
  infer_instance

/-- 適切な共通係数商から各有限段への標準係数射は単射。 -/
theorem Andre.deltaDivisionFiniteNormalizedBaseMap_injective (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Function.Injective (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap D d a u N) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalized_moduleFaithfullyFlat D d a u N
  exact FaithfulSMul.algebraMap_injective
    (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
    (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedBaseFlat

/-! ## 標準有限正規化商から構成した具体的全段環 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedDirectLimit

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 標準有限商射の直系条件。既存の合成・恒等式を再利用する。 -/
instance Andre.deltaDivisionFiniteNormalizedDirectedSystem (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    DirectedSystem (fun N : ℕ => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h) where
  map_self {i} x := by
    change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u (Nat.le_refl i) x = x
    rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_self]
    rfl
  map_map {k j i} hij hjk x :=
    RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_comp D d a u hij hjk) x

/-- BS固有の全段環。直極限一般論はMathlibの有向環直極限を使う。 -/
abbrev Andre.DeltaDivisionFiniteNormalizedDirectLimit (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :=
  DirectLimit (fun N : ℕ => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h)

/-- 各有限段から全段環への標準環射。 -/
def Andre.deltaDivisionFiniteNormalizedDirectLimitOf (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N →+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  DirectLimit.Ring.of _ _ N

/-- 全段環への標準射は任意二段間の塔射と可換。 -/
theorem Andre.deltaDivisionFiniteNormalizedDirectLimitOf_compatible (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m)
    (x : _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u n) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u m
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h x) =
        _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u n x :=
  DirectLimit.Ring.of_f h x

/-- 各有限段から全段環への標準射は単射。 -/
theorem Andre.deltaDivisionFiniteNormalizedDirectLimitOf_injective (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Function.Injective (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N) :=
  DirectLimit.mk_injective
    (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h)
    (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_injective D d a u h) N

/-- 全段環の任意元は具体的有限商のある段の標準像。 -/
theorem Andre.deltaDivisionFiniteNormalizedDirectLimit_exists_stage (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (y : _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u) :
    ∃ N, ∃ x : _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N,
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N x = y := by
  obtain ⟨N, x, hx⟩ := DirectLimit.exists_eq_mk
    (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h) y
  exact ⟨N, x, hx.symm⟩

/-- 適切な共通係数商A/(p,d,a_s)から全段環への具体的射。 -/
def Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a →+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u 0).comp
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseMap D d a u)

/-- 全段係数射は、どの有限段の係数射とも整合する。 -/
theorem Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap_eq_of_comp (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u =
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N).comp
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap D d a u N) := by
  apply RingHom.ext
  intro b
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf_compatible
    D d a u (Nat.zero_le N) (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedInitialBaseMap D d a u b)).symm

/-- 全段係数射は、基底係数の任意有限段での標準商像に一致する。 -/
theorem Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap_mk (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) (b : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u (Ideal.Quotient.mk _ b) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N
        (Ideal.Quotient.mk _ (MvPolynomial.C b)) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap_eq_of_comp D d a u N,
    RingHom.comp_apply, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap_mk]

/-- 適切な共通係数商から全段環への射も単射。 -/
theorem Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap_injective (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    Function.Injective (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap_eq_of_comp D d a u 0]
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf_injective D d a u 0).comp
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap_injective D d a u 0)

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedDirectLimit

/-! ## 全段環と有限商直系の共通係数商上の代数射・線形射 -/

@[expose] public noncomputable section DeltaDivisionFiniteNormalizedDirectLimitAlgebra

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 全段係数射によるA/(p,d,a_s)上の全段環の代数構造。 -/
@[instance_reducible] def Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Algebra (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u).toAlgebra

/-- 標準有限商射は共通係数商上の具体的代数射。 -/
def Andre.deltaDivisionFiniteNormalizedTowerAlgHom (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u n
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u m
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u n →ₐ[
      A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u m := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u n
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u m
  exact { _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap D d a u h with
    commutes' := fun b =>
      RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap_comp D d a u h) b }

/-- 標準有限商射の共通係数商上の線形射。 -/
def Andre.deltaDivisionFiniteNormalizedTowerLinearMap (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) {n m : ℕ} (h : n ≤ m) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u n
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u m
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u n →ₗ[
      A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u m := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u n
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u m
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgHom D d a u h).toLinearMap

/-- 全段への標準射は共通係数商上の具体的代数射。 -/
def Andre.deltaDivisionFiniteNormalizedDirectLimitOfAlgHom (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N →ₐ[
      A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
  exact { _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N with
    commutes' := fun b =>
      (RingHom.congr_fun
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap_eq_of_comp D d a u N) b).symm }

/-- 各段から全段への標準線形射。 -/
def Andre.deltaDivisionFiniteNormalizedDirectLimitOfLinearMap (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N →ₗ[
      A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOfAlgHom D d a u N).toLinearMap

/-- 共通係数商上の線形射も、実際の環直系と同じ直系条件を満たす。 -/
theorem Andre.deltaDivisionFiniteNormalizedLinearDirectedSystem (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    letI := fun N => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
    DirectedSystem (fun N : ℕ => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
      (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h) := by
  let := fun N => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra D d a u N
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectedSystem D d a u

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteNormalizedDirectLimitAlgebra

/-! ## 無限相対自由多項式環から全段正規化環への具体的評価射 -/

@[expose] public noncomputable section DeltaDivisionNormalizedDirectLimitEvaluation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 第n変数は、その変数を含む第n有限段の標準商像として全段環に置く。 -/
def Andre.deltaDivisionNormalizedDirectLimitVariable (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u n
    (Ideal.Quotient.mk _ (MvPolynomial.X (s, Fin.last n)))

/-- 同じ変数の任意後段での標準商像は最初の像と一致する。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitVariable_at_stage (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (s : σ) {n N : ℕ} (h : n ≤ N) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitVariable D d a u s n =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N
        (Ideal.Quotient.mk _ (MvPolynomial.X (s, (⟨n, by omega⟩ : Fin (N + 1))))) := by
  have he := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf_compatible D d a u h
    (Ideal.Quotient.mk _ (MvPolynomial.X (s, Fin.last n)))
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerMap_mk] at he
  have hi : (Fin.last n).castLE (Nat.succ_le_succ h) =
      (⟨n, by omega⟩ : Fin (N + 1)) := Fin.ext rfl
  simpa [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitVariable,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerInclusion, hi] using he.symm

/-- 基底係数と各変数の具体的像による、無限相対自由環から全段環への射。 -/
def Andre.deltaDivisionNormalizedDirectLimitEvaluation (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ →+* _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  MvPolynomial.eval₂Hom
    ((_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u).comp
      (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)))
    (fun z => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitVariable D d a u z.1 z.2)

/-- 評価射は基底係数を適切な共通係数商の像へ送る。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitEvaluation_C (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (b : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u (MvPolynomial.C b) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u (Ideal.Quotient.mk _ b) :=
  MvPolynomial.eval₂Hom_C _ _ b

/-- 評価射は各自由変数を指定した全段像へ送る。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitEvaluation_X (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u (MvPolynomial.X (s, n)) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitVariable D d a u s n :=
  MvPolynomial.eval₂Hom_X' _ _ (s, n)

/-- 評価射の有限初期環への制限は、その段の標準商射と全段への射の合成。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitEvaluation_comp_initial (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u).comp
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom =
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N).comp
        (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a u N)) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    have hc : _root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A (MvPolynomial.C b) =
        MvPolynomial.C b := AlgHom.commutes _ b
    change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A (MvPolynomial.C b)) = _
    rw [hc, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_C,
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap_mk D d a u N]
    rfl
  · intro z
    have hx : _root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A (MvPolynomial.X z) =
        MvPolynomial.X (z.1, z.2.val) := by
      simp [_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap]
    change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A (MvPolynomial.X z)) = _
    rw [hx, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_X]
    exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitVariable_at_stage D d a u z.1
      (Nat.le_of_lt_succ z.2.isLt)

/-- 有限段の任意多項式についての標準商射図式。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitEvaluation_initial (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N (Ideal.Quotient.mk _ f) :=
  RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_comp_initial D d a u N) f

/-- 無限相対自由環から全段正規化環への具体的評価射は全射。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitEvaluation_surjective (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    Function.Surjective (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u) := by
  intro y
  obtain ⟨N, x, hx⟩ := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimit_exists_stage D d a u y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f,
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_initial D d a u N f).trans hx⟩

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedDirectLimitEvaluation

/-! ## 全段評価射の核と具体的正規化関係イデアル -/

@[expose] public noncomputable section DeltaDivisionNormalizedDirectLimitKernel

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 無限相対自由環の任意多項式は有限初期変数の標準包含像。 -/
theorem Andre.relativeFreePolynomial_exists_finite_initial (f : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) :
    ∃ N, ∃ g : MvPolynomial (σ × Fin (N + 1)) A,
      _root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A g = f := by
  classical
  let N := f.vars.sup (fun z => z.2)
  have hfi : Function.Injective (fun z : σ × Fin (N + 1) => (z.1, z.2.val)) := by
    intro x y h
    exact Prod.ext (congrArg (fun z : σ × ℕ => z.1) h)
      (Fin.ext (congrArg (fun z : σ × ℕ => z.2) h))
  have hvars : (f.vars : Set (σ × ℕ)) ⊆
      Set.range (fun z : σ × Fin (N + 1) => (z.1, z.2.val)) := by
    intro z hz
    have hle : z.2 ≤ N := Finset.le_sup hz
    exact ⟨(z.1, ⟨z.2, Nat.lt_succ_of_le hle⟩), rfl⟩
  obtain ⟨g, hg⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range f _ hfi hvars
  exact ⟨N, g, hg⟩

/-- 有限初期多項式の評価が零であることは、実際の有限表示イデアルへの所属。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitEvaluation_initial_eq_zero_iff
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
    (N : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) = 0 ↔
      f ∈ _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a u N := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_initial]
  constructor
  · intro h
    have hz : Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) f = 0 :=
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf_injective D d a u N
        (h.trans (map_zero (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N)).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- 全段評価射の核を有限初期環に戻したイデアルは、その段の表示イデアル。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitEvaluation_ker_comap_initial
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (N : ℕ) :
    Ideal.comap (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom
      (RingHom.ker (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u)) =
      _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a u N := by
  ext f
  change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u
    (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) = 0 ↔ _
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_initial_eq_zero_iff D d a u N f

/-- 各有限表示イデアルの包含像の和で得られる具体的全段関係イデアル。 -/
def Andre.deltaDivisionInfiniteNormalizedPresentationIdeal (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) : Ideal (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) :=
  ⨆ N : ℕ, Ideal.map (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom
    (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a u N)

/-- 全段評価射の核は、具体的全段正規化関係イデアルに一致する。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitEvaluation_ker_eq_infinite_normalized
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    RingHom.ker (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionInfiniteNormalizedPresentationIdeal D d a u := by
  unfold _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionInfiniteNormalizedPresentationIdeal
  apply le_antisymm
  · intro f hf
    change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u f = 0 at hf
    obtain ⟨N, g, rfl⟩ := _root_.SerrePositivity.BhattScholze.Andre.relativeFreePolynomial_exists_finite_initial f
    have hg := (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_initial_eq_zero_iff
      D d a u N g).mp hf
    apply (show Ideal.map (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom
        (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a u N) ≤ _ from
        le_iSup (fun n : ℕ =>
          Ideal.map (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (n + 1) σ A).toRingHom
            (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal D d a u n)) N)
    exact Ideal.mem_map_of_mem _ hg
  · apply iSup_le
    intro N
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 1) σ A g) = 0
    exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_initial_eq_zero_iff D d a u N g).mpr hg

/-- 具体的全段正規化関係イデアルの商は、構成した全段環に同型。 -/
def Andre.deltaDivisionNormalizedDirectLimitQuotientEquiv (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) :
    (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ ⧸
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionInfiniteNormalizedPresentationIdeal D d a u) ≃+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  (Ideal.quotEquivOfEq
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_ker_eq_infinite_normalized D d a u).symm).trans
    ((_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u).quotientKerEquivOfSurjective
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_surjective D d a u))

/-- 全段商表示同型は、元の無限自由環の標準商射を具体的評価射へ送る。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitQuotientEquiv_mk (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (f : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitQuotientEquiv D d a u (Ideal.Quotient.mk _ f) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u f := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- 全段商表示同型は、基底係数の標準商像を全段係数射へ送る。 -/
theorem Andre.deltaDivisionNormalizedDirectLimitQuotientEquiv_C (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) (u : Aˣ) (b : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitQuotientEquiv D d a u
      (Ideal.Quotient.mk _ (MvPolynomial.C b)) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u (Ideal.Quotient.mk _ b) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitQuotientEquiv_mk,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_C]

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedDirectLimitKernel

/-! ## 実際の全δ剰余イデアルのWitt正規化と全段環の比較 -/

@[expose] public noncomputable section DeltaDivisionInfiniteWittNormalization

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- (p,Cd)を加えた実際のδ閉包は、深さN+1有限剰余イデアルの上限。 -/
theorem Andre.deltaDivision_mod_pd_deltaClosure_eq_iSup_finite (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (d : A) (a : σ → A) :
    Ideal.span {(p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
      (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).deltaClosure (_root_.SerrePositivity.BhattScholze.deltaDivisionRelationIdeal d a) =
      ⨆ N : ℕ, Ideal.span {(p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a (N + 1) := by
  let P : Ideal (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) :=
    Ideal.span {(p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d}
  rw [_root_.SerrePositivity.BhattScholze.deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  change P ⊔ (⨆ N, _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N) =
    ⨆ N, P ⊔ _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a (N + 1)
  apply le_antisymm
  · apply sup_le
    · exact (show P ≤ P ⊔ _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a (0 + 1) from le_sup_left).trans
        (le_iSup (fun N => P ⊔ _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a (N + 1)) 0)
    · apply iSup_le
      intro N
      exact (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal_mono D d a (Nat.le_succ N)).trans
        ((show _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a (N + 1) ≤
          P ⊔ _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a (N + 1) from le_sup_right).trans
          (le_iSup (fun N => P ⊔ _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a (N + 1)) N))
  · apply iSup_le
    intro N
    apply sup_le le_sup_left
    exact (le_iSup (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a) (N + 1)).trans le_sup_right

/-- 逆Witt座標射による実際の全δ剰余イデアルの像は全段正規化イデアル。 -/
theorem Andre.deltaDivision_mod_pd_deltaClosure_inverse_map (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ =>
      (p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    Ideal.map (_root_.SerrePositivity.BhattScholze.relativeFreeWittInverseMap D hpA).toRingHom
      (Ideal.span {(p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).deltaClosure (_root_.SerrePositivity.BhattScholze.deltaDivisionRelationIdeal d a)) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionInfiniteNormalizedPresentationIdeal D d a u := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_eq_iSup_finite, Ideal.map_iSup]
  unfold _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionInfiniteNormalizedPresentationIdeal
  congr 1
  funext N
  rw [_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal_inverse_map_eq_first_sup_normalized D hpA hpL hg d a u hu,
    _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal_map_initial D d a u hu]

/-- 実際のmod(p,d)全δ剰余商は、標準有限正規化商からの全段環に同型。 -/
def Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ =>
      (p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).deltaClosure (_root_.SerrePositivity.BhattScholze.deltaDivisionRelationIdeal d a))) ≃+*
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  (Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.relativeFreeWittCoordinateEquiv D hpA).symm.toRingEquiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_inverse_map D hpA hpL hg d a u hu).symm).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitQuotientEquiv D d a u)

/-- 実際の全δ剰余商の比較は、標準商射を逆Witt座標による具体的評価へ送る。 -/
theorem Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv_mk (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ =>
      (p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (f : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu
      (Ideal.Quotient.mk _ f) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation D d a u
        (_root_.SerrePositivity.BhattScholze.relativeFreeWittInverseMap D hpA f) := by
  change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitQuotientEquiv D d a u
    (Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.relativeFreeWittInverseMap D hpA f)) = _
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitQuotientEquiv_mk D d a u _

/-- 実際の全δ剰余商の比較は、基底係数の標準像を全段係数射へ送る。 -/
theorem Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv_C (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A)
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ =>
      (p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (b : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu
      (Ideal.Quotient.mk _ (MvPolynomial.C b)) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u (Ideal.Quotient.mk _ b) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv_mk]
  have hc : _root_.SerrePositivity.BhattScholze.relativeFreeWittInverseMap (σ := σ) D hpA (MvPolynomial.C b) = MvPolynomial.C b :=
    AlgHom.commutes _ b
  rw [hc, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedDirectLimitEvaluation_C]

end SerrePositivity.BhattScholze

end DeltaDivisionInfiniteWittNormalization

/-! ## 実際のraw全δ剰余商の共通係数商上の代数表示 -/

@[expose] public noncomputable section DeltaDivisionInfiniteWittNormalizationAlgebra

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun b : A => (p : A) * b))
variable (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
  (p : RelativeFreeDeltaRing (R := A) σ) * f))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)

/-- 適切な共通係数商から実際のraw mod(p,d)全δ商への具体的係数射。 -/
def Andre.deltaDivision_mod_pd_deltaClosure_baseMap :
    A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a →+*
      (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ ⧸
        (Ideal.span {(p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
          (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).deltaClosure (_root_.SerrePositivity.BhattScholze.deltaDivisionRelationIdeal d a))) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu).symm.toRingHom.comp
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u)

/-- この係数射は元の基底係数の標準商像に一致する。 -/
theorem Andre.deltaDivision_mod_pd_deltaClosure_baseMap_mk (b : A) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_baseMap D hpA hpL hg d a u hu (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (MvPolynomial.C b) := by
  apply (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu).injective
  change (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu)
    ((_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu).symm _) = _
  rw [RingEquiv.apply_symm_apply, _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv_C]

/-- 標準係数射による、適切な共通係数商上の実際のraw全δ剰余商の代数構造。 -/
@[instance_reducible] def Andre.deltaDivision_mod_pd_deltaClosure_baseAlgebra :
    Algebra (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)
      (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ ⧸
        (Ideal.span {(p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
          (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).deltaClosure (_root_.SerrePositivity.BhattScholze.deltaDivisionRelationIdeal d a))) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_baseMap D hpA hpL hg d a u hu).toAlgebra

/-- 実際のraw全δ剰余商と全段環の比較は、標準共通係数射に関する代数同型。 -/
def Andre.deltaDivision_mod_pd_deltaClosure_directLimitAlgEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
    (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).deltaClosure (_root_.SerrePositivity.BhattScholze.deltaDivisionRelationIdeal d a))) ≃ₐ[
      A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
  apply AlgEquiv.ofRingEquiv
    (f := _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu)
  intro b
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv
    D hpA hpL hg d a u hu).apply_symm_apply _

/-- 適切な共通係数商から実際のraw mod(p,d)全δ商への係数射は単射。 -/
theorem Andre.deltaDivision_mod_pd_deltaClosure_baseMap_injective :
    Function.Injective (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_baseMap D hpA hpL hg d a u hu) :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu).symm.injective.comp
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseMap_injective D d a u)

end SerrePositivity.BhattScholze

end DeltaDivisionInfiniteWittNormalizationAlgebra

/-! ## 全段正規化環と具体的加群直極限の比較 -/

@[expose] public noncomputable section DeltaDivisionNormalizedDirectLimitModule

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
attribute [local instance] _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra

/-- 共通係数商上の具体的標準線形塔による、既存の加群直極限。 -/
abbrev Andre.DeltaDivisionNormalizedModuleDirectLimit :=
  Module.DirectLimit (fun N : ℕ => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h)

/-- 各段の標準線形射を既存加群直極限の普遍性で全段環へまとめた射。 -/
def Andre.deltaDivisionNormalizedModuleDirectLimitMap :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionNormalizedModuleDirectLimit D d a u →ₗ[
      A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  Module.DirectLimit.lift (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a) ℕ _ _
    (fun N => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOfLinearMap D d a u N)
    (fun _ _ h x => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf_compatible D d a u h x)

/-- 加群直極限からの射は、各段の標準像を構成済み全段環の標準像へ送る。 -/
theorem Andre.deltaDivisionNormalizedModuleDirectLimitMap_of (N : ℕ)
    (x : _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedModuleDirectLimitMap D d a u
      (Module.DirectLimit.of (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a) ℕ _
        (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h) N x) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N x := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedModuleDirectLimitMap, Module.DirectLimit.lift_of]
  rfl

/-- 構成済み全段環は、共通係数商上の具体的加群直極限と線形同型。 -/
def Andre.deltaDivisionNormalizedModuleDirectLimitEquiv :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionNormalizedModuleDirectLimit D d a u ≃ₗ[
      A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a]
      _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedLinearDirectedSystem D d a u
  apply LinearEquiv.ofBijective (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedModuleDirectLimitMap D d a u)
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨N, y, rfl⟩ := Module.DirectLimit.exists_of x
    rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedModuleDirectLimitMap_of] at hx
    have hy : y = 0 := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf_injective D d a u N
      (hx.trans (map_zero (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N)).symm)
    rw [hy, map_zero]
  · intro y
    obtain ⟨N, x, hx⟩ := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimit_exists_stage D d a u y
    exact ⟨Module.DirectLimit.of (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a) ℕ _
      (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h) N x,
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedModuleDirectLimitMap_of D d a u N x).trans hx⟩

/-- 線形同型も各段の標準像に両立する。 -/
theorem Andre.deltaDivisionNormalizedModuleDirectLimitEquiv_of (N : ℕ)
    (x : _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedModuleDirectLimitEquiv D d a u
      (Module.DirectLimit.of (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a) ℕ _
        (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h) N x) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitOf D d a u N x :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedModuleDirectLimitMap_of D d a u N x

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedDirectLimitModule

/-! ## BSの具体的全段正規化環の共通係数商上の平坦性 -/

@[expose] public noncomputable section DeltaDivisionNormalizedDirectLimitFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
attribute [local instance] _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra
local notation "B" => (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)

/-- BSの具体的標準加群直極限は、適切な共通係数商上平坦。 -/
theorem Andre.deltaDivisionNormalizedModuleDirectLimit_moduleFlat :
    Module.Flat B (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionNormalizedModuleDirectLimit D d a u) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedLinearDirectedSystem D d a u
  let := fun N => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalized_moduleFlat D d a u N
  exact _root_.SerrePositivity.moduleDirectLimit_flat
    (fun N : ℕ => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (fun _ _ h => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h)

/-- 構成済みの全段正規化環は、標準係数射によってA/(p,d,a_s)上平坦。 -/
theorem Andre.deltaDivisionFiniteNormalizedDirectLimit_moduleFlat :
    Module.Flat B (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedModuleDirectLimit_moduleFlat D d a u
  exact Module.Flat.of_linearEquiv (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedModuleDirectLimitEquiv D d a u).symm

/-- 実際のraw mod(p,d)全δ剰余商も、標準係数射によって適切な共通係数商上平坦。 -/
theorem Andre.deltaDivision_mod_pd_deltaClosure_moduleFlat
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ =>
      (p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (hu : (u : A) = D.delta d) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
    Module.Flat B (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).deltaClosure (_root_.SerrePositivity.BhattScholze.deltaDivisionRelationIdeal d a))) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimit_moduleFlat D d a u
  exact Module.Flat.of_linearEquiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitAlgEquiv D hpA hpL hg d a u hu).toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedDirectLimitFlat

/-! ## 有限正規化商の標準射の共通係数商上のテンソル単射性 -/

@[expose] public noncomputable section DeltaDivisionNormalizedTensorTransition

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
attribute [local instance] _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra
local notation "R₀" => (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)

/-- 任意有限段間の標準射は、共通係数商上の任意加群とテンソルしても単射。 -/
theorem Andre.deltaDivisionFiniteNormalizedTower_rTensor_injective
    {n m : ℕ} (h : n ≤ m) (N : Type w) [AddCommGroup N] [Module R₀ N] :
    Function.Injective ((_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h).rTensor N) := by
  let C := _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u n
  let E := _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u m
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
  let : IsScalarTower R₀ C E := IsScalarTower.of_algebraMap_eq
    (fun b => (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseMap_comp D d a u h) b).symm)
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTower_moduleFaithfullyFlat D d a u h
  let t := TensorProduct.mk C E (C ⊗[R₀] N) 1
  have ht : Function.Injective t :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := C) (B := E) (C ⊗[R₀] N)
  let e₁ := (TensorProduct.AlgebraTensorModule.assoc R₀ C C E C N).symm.restrictScalars R₀
  let e₂ := TensorProduct.congr ((TensorProduct.rid C E).restrictScalars R₀) (LinearEquiv.refl R₀ N)
  let e := e₁.trans e₂
  have he : e.toLinearMap.comp (t.restrictScalars R₀) =
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h).rTensor N := by
    apply TensorProduct.ext'
    intro x y
    change e (1 ⊗ₜ[C] (x ⊗ₜ[R₀] y)) =
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h) x ⊗ₜ[R₀] y
    simp only [e, e₁, e₂, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      TensorProduct.AlgebraTensorModule.assoc_symm_tmul, TensorProduct.congr_tmul,
      TensorProduct.rid_tmul, LinearEquiv.refl_apply]
    change (algebraMap C E x * 1) ⊗ₜ[R₀] y = _
    rw [mul_one]
    rfl
  have hi : Function.Injective (e.toLinearMap.comp (t.restrictScalars R₀)) := e.injective.comp ht
  rw [he] at hi
  exact hi

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedTensorTransition

/-! ## BSの具体的全段環とraw全δ商の共通係数商上の忠実平坦性 -/

@[expose] public noncomputable section DeltaDivisionNormalizedDirectLimitFaithfullyFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
attribute [local instance] _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedBaseAlgebra
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra
local notation "R₀" => (A ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) d a)

/-- 各有限段テンソルから具体的テンソル直極限への標準射は単射。 -/
theorem Andre.deltaDivisionNormalizedTensorDirectLimitOf_injective
    (N : Type w) [AddCommGroup N] [Module R₀ N] (n : ℕ) :
    Function.Injective (Module.DirectLimit.of R₀ ℕ
      (fun i => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u i ⊗[R₀] N)
      (fun _ _ h => (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h).rTensor N) n) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedLinearDirectedSystem D d a u
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨m, h, hz⟩ := Module.DirectLimit.of.zero_exact hx
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTower_rTensor_injective D d a u h N
    (hz.trans (map_zero _).symm)

/-- 全段正規化環は標準係数射によってA/(p,d,a_s)上忠実平坦。零係数商も含む。 -/
theorem Andre.deltaDivisionFiniteNormalizedDirectLimit_moduleFaithfullyFlat :
    Module.FaithfullyFlat R₀ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedDirectLimit D d a u) := by
  rw [Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality]
  refine ⟨_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimit_moduleFlat D d a u, ?_⟩
  intro N _ _ hN
  let := hN
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalized_moduleFaithfullyFlat D d a u 0
  let F := fun i j (h : i ≤ j) => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedTowerLinearMap D d a u h
  let e := TensorProduct.congr (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedModuleDirectLimitEquiv D d a u)
    (LinearEquiv.refl R₀ N)
  let l := TensorProduct.directLimitLeft F N
  have hi₁ : Function.Injective
      (TensorProduct.mk R₀ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0) N 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := R₀) (B := _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a u 0) N
  have hi₂ := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedTensorDirectLimitOf_injective D d a u N 0
  have hi := e.injective.comp (l.symm.injective.comp (hi₂.comp hi₁))
  exact hi.subsingleton

/-- 実際のraw mod(p,d)全δ商も標準係数射によって適切な共通係数商上忠実平坦。 -/
theorem Andre.deltaDivision_mod_pd_deltaClosure_moduleFaithfullyFlat
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ =>
      (p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ) → ℕ → _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ))
    (hu : (u : A) = D.delta d) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
    Module.FaithfullyFlat R₀ (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).deltaClosure (_root_.SerrePositivity.BhattScholze.deltaDivisionRelationIdeal d a))) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedDirectLimit_moduleFaithfullyFlat D d a u
  exact Module.FaithfullyFlat.of_linearEquiv R₀ _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivision_mod_pd_deltaClosure_directLimitAlgEquiv D hpA hpL hg d a u hu).toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaDivisionNormalizedDirectLimitFaithfullyFlat
