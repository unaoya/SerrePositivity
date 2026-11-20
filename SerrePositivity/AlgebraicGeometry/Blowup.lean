module


public meta import SerrePositivity.Util.Citation
public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Graded.Subquotient

/-!
概要：KST §5 の古典的 blowup を Rees 代数の Proj から構成する。
方針：単項式射影により Rees 代数を次数付けし、Mathlib の Proj に渡す。
規約：まずアフィン基底を扱う。一般スキームへの貼り合わせとは区別する。
使われ方：KST Lemma 5.6 の冪比較と Stacks 081T の支配構成の基礎。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open Polynomial _root_.AlgebraicGeometry CategoryTheory

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
概要：Rees の零次成分を基礎環上の代数とする。
方針：零次成分との環同型を通して定数を送る。
規約：KST §5 の定数多項式による係数作用。
使われ方：係数環を零次成分に変えても生成元を保つ。
-/
instance reesZeroAlgebra : Algebra R (reesGrade I 0) :=
  Algebra.ofModule
    (fun r p q => Subtype.ext (smul_mul_assoc r p.1 q.1))
    (fun r p q => Subtype.ext (mul_smul_comm r p.1 q.1))

/--
概要：基礎環・Rees 零次成分・Rees 代数の作用は両立する。
方針：代数写像の合成は定数多項式への写像に等しい。
規約：KST §5。作用の塔は実際の環準同型から構成する。
使われ方：次数一生成性を零次成分上に移す。
-/
instance reesZeroScalarTower : IsScalarTower R (reesGrade I 0) (reesAlgebra I) :=
  ⟨fun r p q => smul_mul_assoc r p.1 q⟩

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

/--
概要：アフィン中心 V(I) の Spec R への閉埋め込み。
方針：商準同型に Spec を適用する。
規約：KST §5 の中心は被約化せず I 自身で定義する。
使われ方：例外閉部分スキームをファイバー積として作る。
-/
def affineCenterι : Spec (.of (R ⧸ I)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/--
概要：アフィン中心の包含は閉埋め込み。
方針：商準同型の全射性を使う。
規約：KST §5。中心の有限生成性は不要。
使われ方：基底変換後の例外閉部分スキームの閉性。
-/
instance affineCenterι_isClosedImmersion : IsClosedImmersion (affineCenterι I) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/--
概要：アフィン blowup の例外閉部分スキーム。
方針：中心 V(I) のスキーム論的逆像をファイバー積で定義する。
規約：KST §5。有効 Cartier 因子としての性質は別の主張である。
使われ方：古典的 blowup 正方形の右上隅を与える。
-/
def affineExceptional : Scheme :=
  Limits.pullback (affineBlowupπ I) (affineCenterι I)

/--
概要：例外閉部分スキームの blowup への包含。
方針：ファイバー積の第一射影を使う。
規約：KST §5、スキーム論的逆像の包含である。
使われ方：例外因子の理想層と閉埋め込みの基準射。
-/
def affineExceptionalι : affineExceptional I ⟶ affineBlowup I :=
  Limits.pullback.fst _ _

/--
概要：例外閉部分スキームから中心への構造射。
方針：ファイバー積の第二射影を使う。
規約：KST §5 の blowup 正方形と同じ向き。
使われ方：中心の厚みと例外閉部分スキームの厚みを比較する。
-/
def affineExceptionalToCenter : affineExceptional I ⟶ Spec (.of (R ⧸ I)) :=
  Limits.pullback.snd _ _

set_option backward.isDefEq.respectTransparency false in
/--
概要：例外閉部分スキームの包含は閉埋め込み。
方針：中心の閉埋め込みを基底変換する。
規約：KST §5、固有性とは独立に成立する。
使われ方：抽象 blowup 正方形の閉埋め込みの辺。
-/
instance affineExceptionalι_isClosedImmersion : IsClosedImmersion (affineExceptionalι I) := by
  unfold affineExceptionalι
  infer_instance

/--
概要：アフィン blowup の中心と例外閉部分スキームの正方形は可換。
方針：ファイバー積の射影の交換式を使う。
規約：KST §5、基礎スキームは Spec R。
使われ方：導来 blowup の古典的 truncation との比較。
-/
@[reassoc] theorem affineExceptional_square :
    affineExceptionalι I ≫ affineBlowupπ I =
      affineExceptionalToCenter I ≫ affineCenterι I :=
  Limits.pullback.condition

/--
概要：次数 n の係数 a から Rees の斉次元を作る。
方針：単項式 a t^n とその係数所属証明を組にする。
規約：KST §5、a の所属は I^n。
使われ方：標準チャートと Veronese 比較の生成元。
-/
def reesMonomial (n : ℕ) (a : ↥(I ^ n)) : reesAlgebra I :=
  ⟨monomial n a.1, reesAlgebra.monomial_mem.mpr a.2⟩

/--
概要：Rees 単項式は指定した次数の成分に属する。
方針：係数計算で射影の固定点条件を確認する。
規約：KST §5、零係数も許す。
使われ方：Proj の標準基本開集合の斉次性条件。
-/
lemma reesMonomial_mem (n : ℕ) (a : ↥(I ^ n)) :
    reesMonomial I n a ∈ reesGrade I n :=
  (mem_reesGrade_iff I n _).mpr (by simp [reesMonomial])

/--
概要：a ∈ I に対応する Rees 代数の次数一元。
方針：I^1 = I を使い単項式 a t を作る。
規約：KST §5 の標準 blowup チャートの生成元。
使われ方：D₊(a t) 上のアフィン局所計算。
-/
def reesDegreeOne (a : I) : reesAlgebra I :=
  reesMonomial I 1 ⟨a.1, by simp⟩

/--
概要：a t は Rees 代数の次数一成分に属する。
方針：Rees 単項式の斉次性を適用する。
規約：KST §5、a ∈ I。
使われ方：blowup の標準チャートの Spec 同型。
-/
lemma reesDegreeOne_mem (a : I) : reesDegreeOne I a ∈ reesGrade I 1 :=
  reesMonomial_mem I 1 _

/--
概要：アフィン blowup の標準開集合 D₊(a t)。
方針：Rees 代数の次数一元に Proj の基本開集合を適用する。
規約：KST §5、点集合だけでなく開部分スキームを指定する。
使われ方：例外因子と中心の補開集合上の同型の局所計算。
-/
def affineBlowupChart (a : I) : (affineBlowup I).Opens :=
  Proj.basicOpen (reesGrade I) (reesDegreeOne I a)

/--
概要：標準 blowup チャートは Rees の斉次局所化の零次環の Spec。
方針：Mathlib の Proj の基本アフィン同型を適用する。
規約：KST §5、次数一なので正次数の条件を満たす。
使われ方：チャート環上のイデアルと非零因子の計算。
-/
def affineBlowupChartIso (a : I) : (affineBlowupChart I a).toScheme ≅
    Spec (.of (HomogeneousLocalization.Away (reesGrade I) (reesDegreeOne I a))) :=
  Proj.basicOpenIsoSpec (reesGrade I) _ (reesDegreeOne_mem I a) (by decide)

/--
概要：Rees 代数は基礎環上で次数一元に生成される。
方針：多項式環への単射で adjoin を比較し、Mathlib の生成性を使う。
規約：KST §5、中心の有限生成性は不要。
使われ方：次数一の標準チャートが blowup を被覆することを示す。
-/
lemma rees_adjoin_degreeOne :
    Algebra.adjoin R (Set.range (reesDegreeOne I)) = ⊤ := by
  apply Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top]
  have himage : (reesAlgebra I).val '' Set.range (reesDegreeOne I) =
      (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) := by
    ext p
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨q, ⟨a, rfl⟩, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨reesDegreeOne I ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  rw [himage, adjoin_monomial_eq_reesAlgebra]
  exact (reesAlgebra I).range_val.symm

/--
概要：Rees 代数は零次成分上でも次数一元に生成される。
方針：基礎環上の生成性と係数環拡大を使う。
規約：KST §5、零次成分の係数作用は定数多項式の作用。
使われ方：Proj の標準アフィン被覆の生成性条件。
-/
lemma rees_adjoin_zero_degreeOne :
    Algebra.adjoin (reesGrade I 0) (Set.range (reesDegreeOne I)) = ⊤ := by
  apply top_unique
  intro p _
  have hp : p ∈ Algebra.adjoin R (Set.range (reesDegreeOne I)) := by
    rw [rees_adjoin_degreeOne I]
    trivial
  exact (Algebra.adjoin_le (S := (Algebra.adjoin (reesGrade I 0)
    (Set.range (reesDegreeOne I))).restrictScalars R) (fun a ha =>
    (Algebra.subset_adjoin ha :
      a ∈ Algebra.adjoin (reesGrade I 0) (Set.range (reesDegreeOne I))))) hp

/--
概要：次数一元の標準開集合がアフィン blowup 全体を被覆する。
方針：零次成分上の次数一生成性から Proj の被覆定理を使う。
規約：KST §5、添字は I の全元であり有限生成性を要求しない。
使われ方：例外因子と補開集合の局所計算を大域化する。
-/
theorem iSup_affineBlowupChart : ⨆ a : I, affineBlowupChart I a = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (reesGrade I) (reesDegreeOne I)
    (fun a => ⟨1, reesDegreeOne_mem I a⟩) (rees_adjoin_zero_degreeOne I)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas





















































/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (1.9)" (partial := component) "仮定：固定基底上の有限型スキーム、またはアフィン上の指定された通常ブローアップ（Lean が強い）。結論：抽象正方形の条件と通常例外因子の閉性。アフィン正則列中心の四角形として束ねた宣言は確認できない（Lean が弱い）。"] _root_.SerrePositivity.AlgebraicGeometry.affineExceptionalι_isClosedImmersion
