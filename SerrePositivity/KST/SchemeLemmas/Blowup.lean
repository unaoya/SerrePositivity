module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import SerrePositivity.CommutativeAlgebra.GradedSubquotient

/-!
概要：KST §5 の古典的 blowup を Rees 代数の Proj から構成する。
方針：単項式射影により Rees 代数を次数付けし、Mathlib の Proj に渡す。
規約：まずアフィン基底を扱う。一般スキームへの貼り合わせとは区別する。
使われ方：KST Lemma 5.6 の冪比較と Stacks 081T の支配構成の基礎。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.SchemeLemmas

open Polynomial AlgebraicGeometry CategoryTheory

variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：Rees 代数の次数 n 成分を取り出す R 線形射影。
方針：多項式の係数を取り、その単項式を Rees 代数に戻す。
規約：係数は I^n に属する。KST §5 の通常の Rees 次数を使う。
使われ方：次数成分の内部直和の証明に使う。
-/
def reesProjection (n : ℕ) : reesAlgebra I →ₗ[R] reesAlgebra I :=
  (((monomial n).comp (lcoeff R n)).comp (reesAlgebra I).val.toLinearMap).codRestrict
    (reesAlgebra I).toSubmodule (fun p => reesAlgebra.monomial_coeff_mem p n)

/--
概要：Rees 代数の次数 n の斉次部分加群。
方針：単項式射影の像として定義する。
規約：KST §5 の Rees 代数を多項式環の部分代数として扱う。
使われ方：アフィン blowup の Proj の次数付け。
-/
def reesGrade (n : ℕ) : Submodule R (reesAlgebra I) :=
  (reesProjection I n).range

/--
概要：Rees 単項式射影の多項式としての値。
方針：定義を展開する。
規約：KST §5 の次数 n の係数だけを残す。
使われ方：斉次成分の積と直和を計算する。
-/
@[simp] lemma reesProjection_val (n : ℕ) (p : reesAlgebra I) :
    (reesProjection I n p : R[X]) = monomial n (p.1.coeff n) := rfl

/--
概要：斉次成分への所属は単項式射影の固定点条件と同値。
方針：係数の計算により射影の冪等性を示す。
規約：KST §5、任意の可換環で成立する。
使われ方：次数付き乗法と零次成分の同定。
-/
lemma mem_reesGrade_iff (n : ℕ) (p : reesAlgebra I) :
    p ∈ reesGrade I n ↔ (p : R[X]) = monomial n (p.1.coeff n) := by
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · intro h
    exact ⟨p, Subtype.ext h.symm⟩

/--
概要：Rees の斉次成分は乗法に関して次数を加える。
方針：斉次元を単項式に書き換え、その積を計算する。
規約：KST §5 の加法的な自然数次数。
使われ方：`GradedRing` の乗法構造を与える。
-/
instance reesGradeGradedMonoid : SetLike.GradedMonoid (reesGrade I) where
  one_mem := (mem_reesGrade_iff I 0 1).mpr (by simp)
  mul_mem := by
    intro i j p q hp hq
    apply (mem_reesGrade_iff I (i + j) (p * q)).mpr
    change (p : R[X]) * (q : R[X]) = _
    have hp' := (mem_reesGrade_iff I i p).mp hp
    have hq' := (mem_reesGrade_iff I j q).mp hq
    conv_lhs => rw [hp', hq', monomial_mul_monomial]
    have hcoeff : ((p : R[X]) * (q : R[X])).coeff (i + j) =
        p.1.coeff i * q.1.coeff j := by
      conv_lhs => rw [hp', hq', monomial_mul_monomial]
      exact coeff_monomial_same _ _
    exact congrArg (monomial (i + j)) hcoeff.symm

/--
概要：Rees 代数は各次数成分の内部直和である。
方針：単項式射影の直交性と有限な台による展開を使う。
規約：KST §5。Noether 性も有限生成性も不要。
使われ方：Proj が要求する次数分解の構成。
-/
theorem isInternal_reesGrade : DirectSum.IsInternal (reesGrade I) := by
  classical
  apply SerrePositivity.HilbertSerre.isInternal_of_projections
    (reesGrade I) (reesProjection I)
  · intro n p
    exact Subtype.ext ((mem_reesGrade_iff I n p).mp p.2).symm
  · intro n k hkn p
    apply Subtype.ext
    change monomial n (p.val.val.coeff n) = 0
    rw [(mem_reesGrade_iff I k p).mp p.2, coeff_monomial, ite_eq_right hkn, map_zero]
  · apply top_unique
    intro p _
    rw [reesAlgebra.as_sum_support p]
    apply Submodule.sum_mem
    intro n _
    exact (le_iSup (reesGrade I) n) ⟨p, rfl⟩

/--
概要：Rees 代数に自然数次数の環構造を与える。
方針：内部直和の分解と単項式の積を組み合わせる。
規約：KST §5 の通常の Rees 代数である。
使われ方：blowup を絶対 Proj として定義する。
-/
instance reesGradeGradedRing : GradedRing (reesGrade I) :=
  { reesGradeGradedMonoid I,
    (isInternal_reesGrade I).chooseDecomposition with }

/--
概要：アフィンスキーム Spec R の I に沿う blowup。
方針：Rees 代数の実際の Proj スキームを取る。
規約：KST §5、中心 I は任意。固有性には有限生成性が別途必要。
使われ方：一般スキームへの貼り合わせの局所モデル。
-/
def affineBlowup : Scheme := Proj (reesGrade I)

/--
概要：Rees 代数の零次成分は基礎環と同型。
方針：定数係数と定数多項式を互いに逆の環準同型にする。
規約：KST §5 の零次成分には I の制約がない。
使われ方：blowup の構造射の基底を Spec R に合わせる。
-/
def reesZeroEquiv : reesGrade I 0 ≃+* R where
  toFun p := p.1.1.coeff 0
  invFun r := ⟨algebraMap R (reesAlgebra I) r,
    (mem_reesGrade_iff I 0 _).mpr (by simp)⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((mem_reesGrade_iff I 0 p).mp p.2).symm
  right_inv r := by simp
  map_mul' p q := by
    change ((p.1 : R[X]) * (q.1 : R[X])).coeff 0 = _
    simp
  map_add' p q := by simp

/--
概要：アフィン blowup の Spec R への構造射。
方針：Proj の零次成分への射を零次成分の環同型で移す。
規約：KST §5 の blowup は基礎スキーム上の対象として扱う。
使われ方：固有性・中心の逆像・支配射の交換式の基準射。
-/
def affineBlowupπ : affineBlowup I ⟶ Spec (.of R) :=
  Proj.toSpecZero (reesGrade I) ≫
    Spec.map (CommRingCat.ofHom (reesZeroEquiv I).symm.toRingHom)

/--
概要：有限生成中心の Rees 代数は零次成分上で有限型。
方針：既存の R 上の有限型性から係数環を拡大する。
規約：KST §5、Noether 性ではなく中心の有限生成性だけを使う。
使われ方：Proj の固有性をアフィン blowup に適用する。
-/
lemma rees_finiteType_over_zero (hI : I.FG) :
    Algebra.FiniteType (reesGrade I 0) (reesAlgebra I) := by
  let : Algebra.FiniteType R (reesAlgebra I) :=
    ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
  have hcomp : (algebraMap (reesGrade I 0) (reesAlgebra I)).comp
      (reesZeroEquiv I).symm.toRingHom = algebraMap R (reesAlgebra I) := by
    ext r
    rfl
  apply RingHom.finiteType_algebraMap.mp
  apply RingHom.FiniteType.of_comp_finiteType (f := (reesZeroEquiv I).symm.toRingHom)
  rw [hcomp]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
概要：有限生成イデアルに沿うアフィン blowup の構造射は固有。
方針：有限型次数付き環の Proj の固有性と基底の同型を使う。
規約：KST §5、中心は有限生成と仮定する。
使われ方：抽象 blowup 正方形の固有射を与える。
-/
theorem affineBlowupπ_isProper (hI : I.FG) : IsProper (affineBlowupπ I) := by
  let := rees_finiteType_over_zero I hI
  have : IsIso (CommRingCat.ofHom (reesZeroEquiv I).symm.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (reesZeroEquiv I).symm.bijective
  have : IsProper (Proj.toSpecZero (reesGrade I)) := inferInstance
  have : IsIso (Spec.map (CommRingCat.ofHom (reesZeroEquiv I).symm.toRingHom)) :=
    inferInstance
  have : IsProper (Spec.map (CommRingCat.ofHom (reesZeroEquiv I).symm.toRingHom)) :=
    inferInstance
  unfold affineBlowupπ
  infer_instance

end SerrePositivity.KST.SchemeLemmas
