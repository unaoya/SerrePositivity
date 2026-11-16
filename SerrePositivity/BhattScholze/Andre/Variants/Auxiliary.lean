module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PrincipalDP
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DeltaDivisionWitt
public import Mathlib.RingTheory.TensorProduct.Maps
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootInput
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrismaticResidue
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.BhattScholze.Andre.Perfection.DeltaAlgebra
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import SerrePositivity.BhattScholze.Andre.Envelope.MonicCandidate
public import SerrePositivity.BhattScholze.Andre.Envelope.FamilyEvaluation
public import SerrePositivity.BhattScholze.Andre.Envelope.SourceEvaluation
public import SerrePositivity.HomologicalAlgebra.TorExactColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedTensorBaseChange
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.InputCategory
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.BhattScholze.Andre.Transfinite.Colimit
public import SerrePositivity.BhattScholze.Andre.Perfection.PerfectPrismMonic
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Family
public import SerrePositivity.BhattScholze.Andre.Envelope.JetRegularity
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta

/-!
# 変種のための補題

## 概要
入力作用からの基底保存性、係数自己同型比較の合成、冪零核の商に沿う忠実平坦性、主元完全忠実平坦性と冪、Frobenius 除算の初期係数商、p 正則性を使わないモニック pd 包、任意族の中の有限部分族・有界支持の残余 Tor、根付き拡大の基底同型による移送、整 perfectoid 基底上の有限モニック根付き拡大、係数還元後の pd 包の普遍性と移送、正則主商への完全忠実平坦性の下降、完全 δ 化後の商、半線形同型の底変換。
BS 著者版 Theorem 7.14 と Remark 7.15 に関連する根付き拡大の変種に使う補題を集める。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/FrobeniusPullback`、`PowerRootEnvelope/Initiality`、`PowerRootEnvelope/PerfectionFaithful`、`PowerRootEnvelope/Unconditional/FrobeniusPD`、`PowerRootEnvelope/Unconditional/Localization`、`Variants/ArbitraryFamily`、`Variants/MonicRootedExtension`、`Variants/RootedExtension`。
-/

universe u v w z

/-! ## 係数還元後の実 pd 包の普遍性

## 概要

一次関係商のさらに商 Q が実分冪構造を持ち、入力の分冪が標準生成元の商像なら、
関係式を殺す任意の分冪標的への係数を保つ分冪射は一意に存在する。
BS 著者版 Remark 7.15(1)（著者版 p.62）の係数変更後の実 pd 包を扱う。

## 方針

通常の分冪評価を商へ降ろし、正次数生成元上の分冪合成公式で互換性を示す。
一意性は元の一次関係商の生成元による外延性を使う。

## 規約

商の分冪構造と入力値の公式は明示引数。標的の正則性・標数は要求しない。

## 使われ方

正則係数元による実分冪降下と組み合わせ、降下後の pd 普遍性を証明する。
-/

@[expose] public noncomputable section PrincipalDPQuotientUniversal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (y : A)
local notation "D" => PrincipalDPPresentation A y
variable (K : Ideal (PrincipalDPPresentation A y))
local notation "q" => Ideal.Quotient.mk K
local notation "Q" => D ⧸ K
local notation "J" => Ideal.map q (principalDPPositiveIdeal y)
variable {B : Type v} [CommRing B] [Algebra A B] {I : Ideal B}
variable (Ht : DividedPowers I) (hyB : algebraMap A B y ∈ I)
variable (hK : ∀ t ∈ K, principalDPEval Ht y hyB t = 0)

/-- 概要：標準分冪評価は関係式を殺すなら実商からの射へ降りる。
方針：通常の代数商の普遍射を使う。
規約：関係式は任意のイデアル K で指定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数還元後の評価。 -/
def principalDPQuotientEval : Q →ₐ[A] B :=
  Ideal.Quotient.liftₐ K (principalDPEval Ht y hyB) hK

/-- 概要：商の評価は代表元で元の標準評価に一致する。
方針：商の普遍射の定義を使う。
規約：元の一次関係商の任意の元を扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の射の比較。 -/
theorem principalDPQuotientEval_mk (t : D) :
    principalDPQuotientEval y K Ht hyB hK (q t) = principalDPEval Ht y hyB t := rfl

/-- 概要：商の標準生成元の評価は標的の入力元の分冪。
方針：代表元公式と元の評価公式を使う。
規約：全次数を扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の分冪射の判定。 -/
theorem principalDPQuotientEval_generator (n : ℕ) :
    principalDPQuotientEval y K Ht hyB hK (q (principalDPGenerator y n)) =
      Ht.dpow n (algebraMap A B y) := by
  rw [principalDPQuotientEval_mk, principalDPEval_generator]

variable (Hq : DividedPowers ((principalDPPositiveIdeal y).map (Ideal.Quotient.mk K)))
variable (hγ : ∀ n, Hq.dpow n
  (Ideal.Quotient.mk K (algebraMap A (PrincipalDPPresentation A y) y)) =
    Ideal.Quotient.mk K (principalDPGenerator y n))

include hγ in
/-- 概要：商の標準評価は実分冪構造を保つ。
方針：像イデアルの正次数生成元で分冪合成則を照合する。
規約：商の構造と標準値の公式だけを仮定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実商からの pd 普遍射。 -/
theorem principalDPQuotientEval_isDPMorphism :
    Hq.IsDPMorphism Ht (principalDPQuotientEval y K Ht hyB hK).toRingHom := by
  have hbase : q (algebraMap A D y) ∈ J :=
    Ideal.mem_map_of_mem q (principalDPPositiveIdeal_base_mem y)
  have hspan : J = Ideal.span (Set.range fun k : ℕ => q (principalDPGenerator y (k + 1))) := by
    rw [principalDPPositiveIdeal, Ideal.map_span, ← Set.range_comp']
  apply DividedPowers.IsDPMorphism.on_span Hq Ht hspan
  · rintro t ⟨k, rfl⟩
    change principalDPQuotientEval y K Ht hyB hK (q (principalDPGenerator y (k + 1))) ∈ I
    rw [principalDPQuotientEval_generator]
    exact Ht.dpow_mem (Nat.succ_ne_zero k) hyB
  · rintro n t ⟨k, rfl⟩
    change principalDPQuotientEval y K Ht hyB hK
      (Hq.dpow n (q (principalDPGenerator y (k + 1)))) =
        Ht.dpow n (principalDPQuotientEval y K Ht hyB hK
          (q (principalDPGenerator y (k + 1))))
    rw [← hγ (k + 1), Hq.dpow_comp (Nat.succ_ne_zero k) hbase, map_mul,
      map_natCast, hγ (n * (k + 1)), hγ (k + 1), principalDPQuotientEval_generator,
      principalDPQuotientEval_generator, Ht.dpow_comp (Nat.succ_ne_zero k) hyB]

include hγ hyB hK in
/-- 概要：関係式を殺す任意の分冪標的への係数を保つ分冪射は一意に存在する。
方針：商の標準評価で存在を示し、入力元の分冪から全生成元上の一致を得る。
規約：標的にねじれなし等の追加仮定を置かない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数変更後の pd 普遍性。 -/
theorem existsUnique_principalDPQuotientMorphism :
    ∃! F : Q →ₐ[A] B, Hq.IsDPMorphism Ht F.toRingHom := by
  refine ⟨principalDPQuotientEval y K Ht hyB hK,
    principalDPQuotientEval_isDPMorphism y K Ht hyB hK Hq hγ, ?_⟩
  intro F hF
  apply Ideal.Quotient.algHom_ext
  apply principalDPHom_ext
  intro n
  change F (q (principalDPGenerator y n)) =
    principalDPQuotientEval y K Ht hyB hK (q (principalDPGenerator y n))
  rw [principalDPQuotientEval_generator]
  calc
    F (q (principalDPGenerator y n)) =
        F.toRingHom (Hq.dpow n (q (algebraMap A D y))) := congrArg F (hγ n).symm
    _ = Ht.dpow n (F (q (algebraMap A D y))) :=
      (hF.dpow_comp _ (Ideal.mem_map_of_mem q (principalDPPositiveIdeal_base_mem y))).symm
    _ = Ht.dpow n (algebraMap A B y) := by
      change Ht.dpow n (F (algebraMap A Q y)) = _
      rw [F.commutes]


end SerrePositivity.BhattScholze.Andre

end PrincipalDPQuotientUniversal

/-! ## raw δ 包の係数自己同型比較の合成

## 概要

係数 δ 自己同型を順に適用した raw 除算包の比較射は、合成自己同型の比較射と一致する。
BS 著者版 Remark 7.15（著者版 p.62）の係数成分と指数成分の比較に使う。

## 方針

両射の δ 互換性を確かめ、係数と初期除算変数での外延性を適用する。

## 規約

入力族・分母の正則性や完備性は要求しない。

## 使われ方

係数 Frobenius と指数 p 倍を別々に作用させる raw 射を全体の射と比較する。
-/

@[expose] public noncomputable section DeltaDivisionCoefficientAutComposition

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 概要：raw 包の係数自己同型比較は自己同型の合成と両立する。
方針：係数合成の等式と初期変数の保存を使い、δ 射の外延性で証明する。
規約：e の後に f を適用する向き。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 分解の raw 包への移送。 -/
theorem deltaDivisionCoefficientAutMap_trans
    (D : DeltaStructure p A) (e f : A ≃+* A)
    (he : D.IsDeltaHom D e.toRingHom) (hf : D.IsDeltaHom D f.toRingHom)
    (d : A) (a : σ → A) :
    (deltaDivisionCoefficientAutMap D f hf (e d) (fun s => e (a s))).comp
      (deltaDivisionCoefficientAutMap D e he d a) =
    deltaDivisionCoefficientAutMap D (e.trans f) (hf.comp he) d a := by
  have h₁ := deltaDivisionCoefficientAutMap_spec D e he d a
  have h₂ := deltaDivisionCoefficientAutMap_spec D f hf (e d) (fun s => e (a s))
  have h₃ := deltaDivisionCoefficientAutMap_spec D (e.trans f) (hf.comp he) d a
  apply deltaAdjoinDivisionHom_ext D
    (deltaAdjoinDivisionStructure D (f (e d)) (fun s => f (e (a s)))) d a
    _ _ (h₂.1.comp h₁.1) h₃.1
  · rw [RingHom.comp_assoc, h₁.2.1, ← RingHom.comp_assoc, h₂.2.1, h₃.2.1]
    rfl
  · intro s
    rw [RingHom.comp_apply, h₁.2.2, h₂.2.2]
    exact (h₃.2.2 s).symm

end SerrePositivity.BhattScholze.Andre

end DeltaDivisionCoefficientAutComposition

/-! ## 係数環同型に沿う半線形同型の実底変換

## 概要

係数環同型に沿う半線形環同型は、通常テンソル底変換の代数同型を与える。
BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 引戻しを実際のテンソルで記述する準備。

## 方針

順射はテンソル積の普遍性、逆射は右因子への標準射と逆環同型の合成で構成する。

## 規約

通常の可換環テンソル積を使う。正則性・平坦性・標数の仮定は不要。

## 使われ方

逆 Frobenius 係数入力の表示を元の多項式の表示へ実底変換する。
-/

@[expose] public noncomputable section SemilinearTensorBaseChange

namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
variable {R : Type u} {S : Type v} {B : Type w} {C : Type z}
variable [CommRing R] [CommRing S] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra S C]

/-- 概要：半線形環同型は実テンソル底変換の代数同型を誘導する。
方針：順方向のテンソル普遍射と右因子への逆射を単純テンソル上で照合する。
規約：係数環同型とその係数可換性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数 Frobenius に沿う引戻し。 -/
def tensorBaseChangeAlgEquivOfSemilinearRingEquiv
    (e : R ≃+* S) (F : B ≃+* C)
    (hF : ∀ r : R, F (algebraMap R B r) = algebraMap S C (e r)) :
    let := e.toRingHom.toAlgebra
    S ⊗[R] B ≃ₐ[S] C := by
  let := e.toRingHom.toAlgebra
  let : Algebra R C := ((algebraMap S C).comp e.toRingHom).toAlgebra
  let : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' rfl
  let fB : B →ₐ[R] C := { F.toRingHom with commutes' := hF }
  let fS : S →ₐ[R] C := IsScalarTower.toAlgHom R S C
  let hc : ∀ s b, Commute (fS s) (fB b) := fun _ _ => Commute.all _ _
  let f := (Algebra.TensorProduct.lift fS fB hc).toRingHom
  let g := (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom.comp F.symm.toRingHom
  have hfg : f.comp g = RingHom.id C := by
    apply RingHom.ext
    intro c
    change Algebra.TensorProduct.lift fS fB hc ((1 : S) ⊗ₜ[R] F.symm c) = c
    rw [Algebra.TensorProduct.lift_tmul]
    change fS 1 * F (F.symm c) = c
    rw [map_one, one_mul, RingEquiv.apply_symm_apply]
  have hgf : g.comp f = RingHom.id (S ⊗[R] B) := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul s b =>
      obtain ⟨r, rfl⟩ := e.surjective s
      change (1 : S) ⊗ₜ[R] F.symm
        (Algebra.TensorProduct.lift fS fB hc ((e r) ⊗ₜ[R] b)) = (e r) ⊗ₜ[R] b
      rw [Algebra.TensorProduct.lift_tmul]
      change (1 : S) ⊗ₜ[R] F.symm (algebraMap S C (e r) * F b) = _
      rw [← hF r, ← map_mul, RingEquiv.symm_apply_apply]
      rw [← Algebra.smul_def r b]
      rw [← TensorProduct.smul_tmul r (1 : S) b]
      rw [Algebra.smul_def r (1 : S), RingHom.algebraMap_toAlgebra, mul_one]
      rfl
  refine { RingEquiv.ofRingHom f g hfg hgf with commutes' := ?_ }
  intro s
  change Algebra.TensorProduct.lift fS fB hc (s ⊗ₜ[R] (1 : B)) = algebraMap S C s
  rw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, mul_one]
  rfl

/-- 概要：実底変換同型は単純テンソルを標準係数と半線形像の積へ送る。
方針：テンソル普遍射の単純テンソル公式を使う。
規約：係数環の任意の元と元の代数の任意の元を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実引戻しの標準係数を追跡する。 -/
theorem tensorBaseChangeAlgEquivOfSemilinearRingEquiv_tmul
    (e : R ≃+* S) (F : B ≃+* C)
    (hF : ∀ r : R, F (algebraMap R B r) = algebraMap S C (e r)) (s : S) (b : B) :
    let := e.toRingHom.toAlgebra
    tensorBaseChangeAlgEquivOfSemilinearRingEquiv e F hF (s ⊗ₜ[R] b) =
      algebraMap S C s * F b := by
  let := e.toRingHom.toAlgebra
  rfl

end SerrePositivity.BhattScholze.Andre

end SemilinearTensorBaseChange

/-! ## 係数を保つ同型に沿う実 pd 包の源への移送

## 概要

主分冪表示との代数同型は、源の実分冪構造・入力元の分冪値・pd 普遍性を与える。
BS 著者版 Remark 7.15(1)（著者版 p.62）の実テンソル側を pd 包として扱う準備。

## 方針

正次数イデアルを逆同型で写し、両方向が分冪射となることから普遍性を移す。

## 規約

係数作用を保つ代数同型と比較先の実分冪構造を明示する。ねじれや完備性は不要。

## 使われ方

根変数上で自然性を検証した実 Frobenius テンソルに分冪包の構造を戻す。
-/

@[expose] public noncomputable section PrincipalPDSourceTransport

namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (y : A)
variable {B : Type v} [CommRing B] [Algebra A B]
variable (e : B ≃ₐ[A] PrincipalDPPresentation A y)

/-- 概要：実同型の源の分冪イデアルは正次数イデアルの逆像として指定する。
方針：逆環同型による像イデアルを使う。
規約：同じ源環のイデアルを構成する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 源のイデアル。 -/
def principalPDSourceIdeal : Ideal B :=
  (principalDPPositiveIdeal y).map e.symm.toRingHom

/-- 概要：同型の源にも比較先から実分冪構造を戻せる。
方針：逆環同型による分冪構造の移送を使う。
規約：比較先の分冪構造を明示する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実テンソル上の構造。 -/
def principalPDSourceDividedPowers (Hs : DividedPowers (principalDPPositiveIdeal y)) :
    DividedPowers (principalPDSourceIdeal y e) :=
  DividedPowers.ofRingEquiv rfl Hs

/-- 概要：源の分冪イデアルは元の入力元の係数像を含む。
方針：比較先での入力元の所属と逆代数同型の係数可換性を使う。
規約：同じ入力 y の像を扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 包の入力条件。 -/
theorem principalPDSourceIdeal_base_mem : algebraMap A B y ∈ principalPDSourceIdeal y e := by
  rw [← e.symm.commutes y]
  exact Ideal.mem_map_of_mem e.symm.toRingHom (principalDPPositiveIdeal_base_mem y)

/-- 概要：源の分冪構造に対して順同型は分冪射。
方針：像イデアルの逆合成と移送された分冪の定義を使う。
規約：比較先の実分冪構造を保つ。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 普遍性の移送。 -/
theorem principalPDSourceEquiv_isDPMorphism (Hs : DividedPowers (principalDPPositiveIdeal y)) :
    (principalPDSourceDividedPowers y e Hs).IsDPMorphism Hs e.toRingHom := by
  refine ⟨?_, ?_⟩
  · exact le_of_eq ((principalDPPositiveIdeal y).map_of_equiv e.symm.toRingEquiv)
  · intro n b hb
    change Hs.dpow n (e b) = e (e.symm (Hs.dpow n (e b)))
    exact (e.apply_symm_apply _).symm

/-- 概要：逆同型も比較先から源への分冪射。
方針：移送イデアルの定義と分冪作用の移送公式を使う。
規約：順逆の実構造を同じものに固定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の普遍射の一意性。 -/
theorem principalPDSourceEquiv_symm_isDPMorphism
    (Hs : DividedPowers (principalDPPositiveIdeal y)) :
    Hs.IsDPMorphism (principalPDSourceDividedPowers y e Hs) e.symm.toRingHom := by
  refine ⟨le_rfl, ?_⟩
  intro n a ha
  exact DividedPowers.ofRingEquiv_dpow_apply rfl Hs

/-- 概要：源の入力元の標準分冪値は比較先の標準生成元の逆像。
方針：逆同型の分冪射性と係数可換性を使う。
規約：全次数 n の入力値を明示する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 生成元。 -/
theorem principalPDSourceDividedPowers_base_apply
    (Hs : DividedPowers (principalDPPositiveIdeal y))
    (hγ : ∀ n, Hs.dpow n (algebraMap A (PrincipalDPPresentation A y) y) =
      principalDPGenerator y n) (n : ℕ) :
    (principalPDSourceDividedPowers y e Hs).dpow n (algebraMap A B y) =
      e.symm (principalDPGenerator y n) := by
  rw [← e.symm.commutes y]
  change (principalPDSourceDividedPowers y e Hs).dpow n
    (e.symm.toRingHom (algebraMap A (PrincipalDPPresentation A y) y)) = _
  rw [(principalPDSourceEquiv_symm_isDPMorphism y e Hs).dpow_comp _
    (principalDPPositiveIdeal_base_mem y), hγ]
  rfl

/-- 概要：同じ実同型の源から任意の分冪標的への係数を保つ分冪射は一意に存在。
方針：比較先の普遍射を順同型と合成し、一意性は逆同型で戻して使う。
規約：標的の宇宙・ねじれ・完備性を制約しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実テンソルを pd 包とする普遍性。 -/
theorem existsUnique_principalPDSourceMorphism
    (Hs : DividedPowers (principalDPPositiveIdeal y))
    (hγ : ∀ n, Hs.dpow n (algebraMap A (PrincipalDPPresentation A y) y) =
      principalDPGenerator y n)
    {C : Type w} [CommRing C] [Algebra A C] {I : Ideal C}
    (Ht : DividedPowers I) (hyC : algebraMap A C y ∈ I) :
    ∃! F : B →ₐ[A] C,
      (principalPDSourceDividedPowers y e Hs).IsDPMorphism Ht F.toRingHom := by
  obtain ⟨F, hF, huniq⟩ := existsUnique_principalDPPositiveMorphism y Hs hγ Ht hyC
  refine ⟨F.comp e.toAlgHom, ?_, ?_⟩
  · exact DividedPowers.IsDPMorphism.comp Ht hF (principalPDSourceEquiv_isDPMorphism y e Hs)
  · intro G hG
    have hG' := DividedPowers.IsDPMorphism.comp Ht hG
      (principalPDSourceEquiv_symm_isDPMorphism y e Hs)
    have heq := huniq (G.comp e.symm.toAlgHom) hG'
    apply AlgHom.ext
    intro b
    simpa only [AlgHom.comp_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_toAlgHom] using
      DFunLike.congr_fun heq (e b)

/-- 概要：係数を保つ主分冪表示への同型は通常多項式の評価も保つ。
方針：同型の単射性で比較先へ移し、評価と環射の可換性を使う。
規約：係数環作用と入力変数の像を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自然な実テンソルで元の f を評価する。 -/
theorem principalPDSourcePolynomialEvaluation
    {K : Type w} [CommRing K] [Algebra K A] [Algebra K B]
    [Algebra K (PrincipalDPPresentation A y)]
    (x : A) (b : B)
    (hK : ∀ r : K, e (algebraMap K B r) = algebraMap K (PrincipalDPPresentation A y) r)
    (hA : ∀ r : K, algebraMap A (PrincipalDPPresentation A y) (algebraMap K A r) =
      algebraMap K (PrincipalDPPresentation A y) r)
    (hx : e b = algebraMap A (PrincipalDPPresentation A y) x) (g : Polynomial K) :
    algebraMap A B (g.eval₂ (algebraMap K A) x) = g.eval₂ (algebraMap K B) b := by
  have hc : e.toRingHom.comp (algebraMap K B) = algebraMap K (PrincipalDPPresentation A y) :=
    RingHom.ext hK
  have hca : (algebraMap A (PrincipalDPPresentation A y)).comp (algebraMap K A) =
      algebraMap K (PrincipalDPPresentation A y) := RingHom.ext hA
  have heval := Polynomial.hom_eval₂ g (algebraMap K B) e.toRingHom b
  rw [hc] at heval
  change e (g.eval₂ (algebraMap K B) b) =
    g.eval₂ (algebraMap K (PrincipalDPPresentation A y)) (e b) at heval
  rw [hx] at heval
  apply e.injective
  calc
    e (algebraMap A B (g.eval₂ (algebraMap K A) x)) =
        algebraMap A (PrincipalDPPresentation A y) (g.eval₂ (algebraMap K A) x) := e.commutes _
    _ = g.eval₂ (algebraMap K (PrincipalDPPresentation A y))
        (algebraMap A (PrincipalDPPresentation A y) x) := by
      rw [Polynomial.hom_eval₂, hca]
    _ = e (g.eval₂ (algebraMap K B) b) := heval.symm

end SerrePositivity.BhattScholze.Andre

end PrincipalPDSourceTransport

/-! ## prism 商の p 正則性を使わないモニック pd 包

## 概要

完全 prism 上のモニック入力について、R/ϖ と R/p の無限根標準表示に
実分冪構造・入力分冪公式・pd 普遍性を与える。
BS 著者版 Remark 7.15(1)（著者版 p.62）の係数還元における追加正則性を解消する。

## 方針

正次数商の自由性から任意係数元による分冪降下を使い、ϖ の持上げで還元する。
原典とは異なる線形切断・実環同型・分冪構造の移送による証明。

## 規約

完全 prism と入力のモニック性のみを使い、prism 商の p 正則性・正次数を仮定しない。
二つの係数環を明示し、mod p 側の入力は元の f の係数像とする。

## 使われ方

A 全体の実 Frobenius 引戻しに、追加正則性なしの実分冪構造と pd 普遍性を供給する。
-/

@[expose] public noncomputable section MonicPerfectPrismPDEnvelope

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
section Native
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "N" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial R₀ p hp
local notation "z" => powerRootCoefficientPDInput p f
local notation "D" => PowerRootCoefficientPDEnvelope p f
local notation "a" => Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)
local notation "K" => Ideal.span {algebraMap R₀ D a}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp (f.map barr)
local notation "Dv" => PrincipalDPPresentation Nv zv

/-- 概要：原典の係数環上のモニック入力の標準表示に実分冪構造を与える。
方針：射影的な正次数商により還元した構造を表示環同型で移す。
規約：prism 商の p 正則性を要求せず、モニック性のみを使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の構造。 -/
def perfectPrismVarpiNativeDividedPowersOfMonic
    (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal zv) :=
  DividedPowers.ofRingEquiv (perfectPrismVarpiPDEnvelopeEquiv_positiveIdeal W hW f)
    (powerRootCoefficientPDReductionOfMonic p W hW f hf a)

/-- 概要：原典の係数環上でも入力元の分冪は全標準生成元に一致する。
方針：移送公式と還元前の標準値の公式、同型の入力・生成元の比較を使う。
規約：全次数 n を含む。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 普遍性への入力。 -/
theorem perfectPrismVarpiNativeDividedPowersOfMonic_base_apply
    (hf : f.Monic) (n : ℕ) :
    (perfectPrismVarpiNativeDividedPowersOfMonic W hW f hf).dpow n
      (algebraMap Nv Dv zv) = principalDPGenerator zv n := by
  rw [← perfectPrismVarpiPDEnvelopeEquiv_input W hW f,
    perfectPrismVarpiNativeDividedPowersOfMonic, DividedPowers.ofRingEquiv_dpow_apply,
    powerRootCoefficientPDReductionOfMonic_base_apply,
    perfectPrismVarpiPDEnvelopeEquiv_generator]

/-- 概要：原典の係数環上の実 pd 包から任意の分冪標的への射は一意に存在する。
方針：移送済みの実分冪構造と標準値を一般の pd 普遍性へ供給する。
規約：標的は無限根環 Nv の任意の代数。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック入力の実 pd 包の同定。 -/
theorem existsUnique_perfectPrismVarpiNativePDMorphismOfMonic
    (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra Nv B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Nv B zv ∈ I) :
    ∃! F : Dv →ₐ[Nv] B,
      (perfectPrismVarpiNativeDividedPowersOfMonic W hW f hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism zv
    (perfectPrismVarpiNativeDividedPowersOfMonic W hW f hf)
    (perfectPrismVarpiNativeDividedPowersOfMonic_base_apply W hW f hf) Ht hzB

end Native

section Prime
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p hp
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Rp" => (A ⧸ W.ideal) ⧸ Ideal.span {(p : A ⧸ W.ideal)}
local notation "Nv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rv p hp
local notation "Np" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial Rp p hp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "bv" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ W.ideal)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW

variable (f : Polynomial A)
local notation "zv" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rv p hp
  (Polynomial.map bv (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "zp" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "Dp" => PrincipalDPPresentation Np zp

local notation "fInv" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "hMonicInv" => perfectPrismInverseFrobeniusPolynomial_monic W hW f
local notation "rootEq" => powerRootVarpiPrimeFrobeniusEquiv W hW
local notation "hInput" => powerRootVarpiPrimeFrobeniusEquiv_input W hW f

/-- 概要：元の mod p 入力の標準表示は実分冪構造を持つ。
方針：逆係数入力の実分冪構造を入力を保つ係数環同型で移す。
規約：prism 商の p 正則性を要求せず、モニック性のみを使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の同定。 -/
def powerRootPrimeFrobeniusDividedPowersOfMonic
    (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal zp) :=
  principalDPTransportDividedPowers rootEq zv zp hInput
    (perfectPrismVarpiNativeDividedPowersOfMonic W hW fInv (hMonicInv hf))

/-- 概要：元の入力の n 次分冪は n 次標準生成元。
方針：入力を保つ係数移送の分冪公式と元の標準値を使う。
規約：零次数を含む全次数を扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 普遍性の入力。 -/
theorem powerRootPrimeFrobeniusDividedPowersOfMonic_base_apply
    (hf : f.Monic) (n : ℕ) :
    (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf).dpow n
      (algebraMap Np Dp zp) = principalDPGenerator zp n :=
  principalDPTransportDividedPowers_base_apply rootEq zv zp hInput
    (perfectPrismVarpiNativeDividedPowersOfMonic W hW fInv (hMonicInv hf))
    (perfectPrismVarpiNativeDividedPowersOfMonic_base_apply W hW fInv (hMonicInv hf)) n

/-- 概要：元の mod p 入力の実分冪包から任意の分冪標的への射は一意に存在。
方針：標準分冪値を持つ一次関係商の一般普遍性を適用する。
規約：標的は Np の任意の代数と分冪イデアル。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実テンソル比較先の pd 包性。 -/
theorem existsUnique_powerRootPrimeFrobeniusPDMorphismOfMonic
    (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra Np B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Np B zp ∈ I) :
    ∃! F : Dp →ₐ[Np] B,
      (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism zp
    (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf)
    (powerRootPrimeFrobeniusDividedPowersOfMonic_base_apply W hW f hf) Ht hzB

end Prime
end SerrePositivity.BhattScholze.Andre

end MonicPerfectPrismPDEnvelope

/-! ## 正則主商への完全忠実平坦性の下降

## 概要

基底と代数で正則な d による通常商は、元の (p,d) 完全忠実平坦性から p 完全忠実平坦性を得る。
BS 著者版 Remark 7.15（著者版 p.62）の最終生成元商への移送。

## 方針

正則主商の導来比較と二元剰余の二段階比較を合成し、同じ剰余 H⁰ の忠実平坦性を戻す。

## 規約

通常商には標準主商代数作用を使う。完備性・Noether 性・prism 構造は不要。

## 使われ方

具体的な完全 δ 化後の生成元商の p 完全忠実平坦性を証明する。
-/

@[expose] public noncomputable section RegularQuotientCompleteFaithful

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra

/-- 概要：正則主商への二元完全忠実平坦性の下降。
方針：導来主剰余と通常主商を比較し、二段階剰余の離散性と忠実平坦性を移す。
規約：元の標準代数作用とその標準主商作用を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商の平坦性。 -/
theorem completelyFaithfullyFlat_principal_quotient_of_pair
    {A : Type u} [CommRing A] (p : ℕ) (d : A) (hd : IsSMulRegular A d)
    (S : Type u) [CommRing S] [Algebra A S]
    (hSd : IsSMulRegular S (algebraMap A S d))
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {(p : A), d}) S) :
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ Ideal.span {d})})
      (S ⧸ Ideal.span {algebraMap A S d}) := by
  let qd := Ideal.Quotient.mk (Ideal.span {d})
  let q := Ideal.Quotient.mk (Ideal.span {(p : A), d})
  let qp := Ideal.Quotient.mk (Ideal.span {(p : A ⧸ Ideal.span {d})})
  let M := ModuleCat.of A S
  let N := ModuleCat.of (A ⧸ Ideal.span {d}) (S ⧸ Ideal.span {algebraMap A S d})
  let X := boundedAboveDerivedSingleFunctor.obj M
  have hMd : IsSMulRegular M d := by
    intro x y hxy
    apply hSd
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using hxy
  let ed := boundedAboveDerivedBaseChangeModuleAugmentationIso qd M
      (scalarExtensionTorVanishing_principal_of_regular d hd M hMd) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (principalScalarExtensionAlgebraQuotientEquiv d S).toModuleIso
  have hz (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), d})) i).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) := by
    let e := boundedAboveDerivedBaseChangeModuleAugmentationIso q M
      (scalarExtensionTorVanishing_of_completelyFlat _ M hS.1)
    exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q).obj M) i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (DerivedCategory.Minus.ι.mapIso e))
  have hf : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), d})) 0).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) := by
    let := scalarExtension_faithfullyFlat_of_completelyFaithfullyFlat _ M hS
    exact Module.FaithfullyFlat.of_linearEquiv _ ((ModuleCat.extendScalars q).obj M)
      ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv
  have hzN (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) i).obj
        ((boundedAboveDerivedBaseChange qp).obj (boundedAboveDerivedSingleFunctor.obj N)).obj) := by
    let HQ (b : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (A ⧸ Ideal.span {(p : A), b})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), b}))).obj X).obj)
    have hq : HQ (d ^ 1) := Eq.mp (congrArg HQ (pow_one d).symm) (hz i hi)
    let HW (b : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat ((A ⧸ Ideal.span {b}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {b})})) i).obj
      ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ Ideal.span {b})}))).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj X)).obj)
    have hw : HW (d ^ 1) := prismaticGeneratorPowerModP_homology_isZero p d 1 X i hq
    have h' : HW d := Eq.mp (congrArg HW (pow_one d)) hw
    exact h'.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso ed))).symm
  have hfN : Module.FaithfullyFlat
      ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})
      ((ModuleCat.extendScalars qp).obj N) := by
    let HQ (b : A) := Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), b})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), b})) 0).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), b}))).obj X).obj)
    have hq : HQ (d ^ 1) := Eq.mp (congrArg HQ (pow_one d).symm) hf
    let HW (b : A) := Module.FaithfullyFlat
      ((A ⧸ Ideal.span {b}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {b})})
      ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {b}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {b})})) 0).obj
        ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ Ideal.span {b})}))).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj X)).obj)
    have hw : HW (d ^ 1) := prismaticGeneratorPowerModPH0_faithfullyFlat p d 1 X hq
    have h' : HW d := Eq.mp (congrArg HW (pow_one d)) hw
    let : Module.FaithfullyFlat
        ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})
        ((DerivedCategory.homologyFunctor
          (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) 0).obj
          ((boundedAboveDerivedBaseChange qp).obj
            ((boundedAboveDerivedBaseChange qd).obj X)).obj) := h'
    let e := (DerivedCategory.homologyFunctor
      (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso ed))
    let : Module.FaithfullyFlat
        ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})
        ((DerivedCategory.homologyFunctor
          (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) 0).obj
          ((boundedAboveDerivedBaseChange qp).obj (boundedAboveDerivedSingleFunctor.obj N)).obj) :=
      Module.FaithfullyFlat.of_linearEquiv _
        ((DerivedCategory.homologyFunctor
          (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) 0).obj
          ((boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange qd).obj X)).obj)
        e.toLinearEquiv.symm
    exact Module.FaithfullyFlat.of_linearEquiv _
      ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) 0).obj
        ((boundedAboveDerivedBaseChange qp).obj (boundedAboveDerivedSingleFunctor.obj N)).obj)
      ((boundedAboveDerivedBaseChangeModuleH0Iso qp).app N).toLinearEquiv.symm
  have ht : scalarExtensionTorVanishing qp N := by
    apply (derivedModuleBaseChange_negative_homology_vanishes_iff qp N).mp
    intro n hn
    exact (hzN (-(n : ℤ)) (by omega)).of_iso
      ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).mapIso
        ((boundedAboveDerivedBaseChangeModuleNatIso qp).app N)).symm
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction _ N ht hfN.1, ?_⟩
  let := hfN
  let e := (quotientScalarExtensionEquiv (Ideal.span {(p : A ⧸ Ideal.span {d})}) N).trans
    (quotientTensorReductionEquiv (Ideal.span {(p : A ⧸ Ideal.span {d})}) N).symm
  exact Module.FaithfullyFlat.of_linearEquiv _ ((ModuleCat.extendScalars qp).obj N) e.symm

end SerrePositivity.BhattScholze.Andre

end RegularQuotientCompleteFaithful

/-! ## 完全 δ 化後の任意の同じ生成元商

## 概要

完全 δ 基底上の実剰余入力から、完全化後の生成元商の自然な射は p 完全忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の最終商への一般移送。

## 方針

二元完全忠実平坦性を正則主商へ下降し、生成元の等式で同じ商の別表記へ移す。

## 規約

原典とは異なる Tor 底変換による経路。導来剰余の離散性・忠実平坦性を明示引数とする。

## 使われ方

元の無限根モニック候補には実剰余の検証済み入力を適用する。
-/

@[expose] public noncomputable section PerfectedDeltaAlgebraQuotientFaithful

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (E : DeltaStructure p B) (j : A →+* B)
variable (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
variable
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
    (hFF : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
local notation "C" => DeltaPerfection E
local notation "κ" => deltaAlgebraPerfectionCoefficient E j
local notation "R" => A ⧸ Ideal.span {OrientedPrism.generator P}

/-- 概要：完全化の指定生成元商への標準基底射。
方針：生成元の係数像との等式を用いて通常主商へ降ろす。
規約：商に使う元 b を明示し、生成元像と等しいことを要求する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の異なる生成元表記の照合。 -/
def perfectedDeltaAlgebraQuotientBaseMap (b : C) (hb : κ P.generator = b) :
    let := pdCompletionCommRing C p b
    R →+* (PDCompletionH0 C p b ⧸ Ideal.span {pdCompletionUnit C p b b}) := by
  let := pdCompletionCommRing C p b
  let v := pdCompletionUnit C p b
  let q := Ideal.Quotient.mk (Ideal.span {v b})
  apply Ideal.Quotient.lift (Ideal.span {P.generator}) (q.comp (v.comp κ))
  change Ideal.span {P.generator} ≤ RingHom.ker (q.comp (v.comp κ))
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  change q (v (κ P.generator)) = 0
  rw [hb]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 概要：標準基底射は元の基底係数の像を保つ。
方針：通常主商の降下射の代表元公式。
規約：b の等式の証明の選択には依存しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的基底射の照合。 -/
theorem perfectedDeltaAlgebraQuotientBaseMap_mk (b : C) (hb : κ P.generator = b) (r : A) :
    let := pdCompletionCommRing C p b
    perfectedDeltaAlgebraQuotientBaseMap P E j b hb (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk (Ideal.span {pdCompletionUnit C p b b})
        (pdCompletionUnit C p b (κ r)) := rfl

include hP hj hzero hFF in
/-- 概要：完全化後の指定生成元商の自然な基底射は p 完全忠実平坦。
方針：生成元の等式で標準表記へ戻し、二元完全忠実平坦性を正則主商へ下降する。
規約：同じ実剰余入力と自然な基底作用を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終 perfectoid 候補。 -/
theorem perfectedDeltaAlgebraQuotientBaseMap_completelyFaithfullyFlat
    (b : C) (hb : κ P.generator = b) :
    let := pdCompletionCommRing C p b
    let := (perfectedDeltaAlgebraQuotientBaseMap P E j b hb).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (PDCompletionH0 C p b ⧸ Ideal.span {pdCompletionUnit C p b b}) := by
  subst b
  let := pdCompletionCommRing C p (κ P.generator)
  let H := PDCompletionH0 C p (κ P.generator)
  let v := pdCompletionUnit C p (κ P.generator)
  let t := v.comp κ
  let : Algebra A H := t.toAlgebra
  have hk := deltaAlgebraPerfectionCoefficient_isDeltaHom P.deltaStructure E j hj
  have hd := hk.map_isDistinguished (P.isDistinguished_generator)
  have hreg : IsSMulRegular H (algebraMap A H P.generator) :=
    (perfectDeltaPDPrism (deltaPerfectionStructure E) (deltaPerfection_isPerfect E)
      (κ P.generator) hd).generator_regular
  have hcf : IsCompletelyFaithfullyFlat (Ideal.span {(p : A), P.generator}) H :=
    isCompletelyFaithfullyFlat_of_linearEquiv _ (baseChangeScalarAlgebraEquiv (B := H))
      (perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat P E j hP hj hzero hFF)
  have h := completelyFaithfullyFlat_principal_quotient_of_pair p P.generator
    P.generator_regular H hreg hcf
  have ha : (perfectedDeltaAlgebraQuotientBaseMap P E j (κ P.generator) rfl).toAlgebra =
      principalAdicQuotientAlgebra P.generator H := by
    apply Algebra.algebra_ext
    intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rfl
  rw [ha]
  exact h

end SerrePositivity.BhattScholze.Andre

end PerfectedDeltaAlgebraQuotientFaithful

/-! ## 任意モニック族内の有限部分族の実残余 Tor

## 概要

任意モニック族内の有限部分族について、全ての有界 δ 深さの実評価関係は
Koszul 分解を与え、対応する実源グラフ商の高次 Tor は零となる。
BS 著者版 Remark 7.15（著者版 p.62）の任意族への実余極限の入力。

## 方針

モニック族の最初の弱正則列を既存の部分族分離と δ 深さの帰納へ渡す。
源グラフの Koszul 分解と標準残余係数射により Tor を同定する。
原典の BS 著者版 Proposition 7.11 による証明とは異なる具体的 PD 計算の経路。

## 規約

添字型全体の有限性は要求しない。係数環の p 正則性と δ(d) の単元性を明示する。
正次数はここでは不要。

## 使われ方

有界深さ有限部分族図式の全段の Tor 消滅を供給する。
-/

@[expose] public noncomputable section MonicPrismaticFiniteSubfamilyTor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (T : Set σ) (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
variable {m : ℕ} (s : Fin m ≃ T)
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => (fun t : σ => monicRelation (f t) t)
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₁" => Ideal.Quotient.mk K₁
local notation "α₁" => deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d)
local notation "cs" N => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N

/-- 概要：任意モニック族の有限部分族の有界深さ実評価列は Koszul 分解を与える。
方針：モニック初項の弱正則性を一般部分族の δ 帰納へ渡す。
規約：全添字型の有限性と正次数は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実余極限での Tor 消滅。 -/
theorem monicPrismaticFiniteSubfamilyEvaluation_isKoszulResolution (N : ℕ)
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (cs N).length =>
      q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs N).get i).1 ((cs N).get i).2)) := by
  have hpP : IsSMulRegular P₁ (p : P₁) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₁)
  let vP := v.map (MvPolynomial.C : A →+* P₁).toMonoidHom
  have hvP : (vP : P₁) = (E₁).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, polynomialRankOneDeltaStructure_delta_C]
  let η : σ × ℕ → L₁ ⧸ K₁ := fun z =>
    q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁ z.1 z.2)
  change SerrePositivity.IsKoszulResolution (η ∘ (cs N).get)
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [← List.map_ofFn, List.ofFn_get]
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSubfamilyEvaluationList_isWeaklyRegular
    T E₁ (MvPolynomial.C d) c₁ s hpP vP hvP
    (monicPrismaticFirstRelation_mod_pd_fin_isWeaklyRegular D d f hf
      (fun i => (s i : σ)) (Subtype.coe_injective.comp s.injective)) N

/-- 概要：有限部分族の実源グラフ商の Tor は実残余評価 Koszul ホモロジーと同型。
方針：源グラフの分解と実残余係数射の関係式を使う。
規約：この比較にはモニック性も p 正則性も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有界深さ入力。 -/
def monicPrismaticFiniteSubfamilySourceTorIso (N i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} ((q₁).comp α₁)).leftDerived i).obj
      (ModuleCat.of L₁ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs N).get)) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (cs N).length =>
        q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
          ((cs N).get j).1 ((cs N).get j).2))).homology (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₁).comp α₁)
    (fun j : Fin (cs N).length => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E₁ c₁ ((cs N).get j))
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_fin_isKoszulResolution E₁ c₁ (cs N).get
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_nodup _
        (Subtype.coe_injective.comp s.injective) N).injective_get) i
  have he : ((q₁).comp α₁) ∘
      (fun j : Fin (cs N).length => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E₁ c₁ ((cs N).get j)) =
      (fun j : Fin (cs N).length => q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs N).get j).1 ((cs N).get j).2)) := by
    funext j
    exact congrArg q₁ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_map E₁ (MvPolynomial.C d) c₁ ((cs N).get j))
  rw [he] at e
  exact e

/-- 概要：任意モニック族内の有限部分族の有界深さ源グラフ商の高次 Tor は零。
方針：実残余評価の Koszul 分解の非零次数消滅を Tor 比較で戻す。
規約：係数環の p 正則性と δ(d) の単元性だけを補助前提とする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限部分族図式。 -/
theorem monicPrismaticFiniteSubfamilySource_tor_subsingleton (N : ℕ)
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₁).comp α₁) (i + 1)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs N).get)) := by
  have hr := monicPrismaticFiniteSubfamilyEvaluation_isKoszulResolution T D d f s N hf hpA v hv
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (monicPrismaticFiniteSubfamilySourceTorIso T D d f s N (i + 1))
  exact ModuleCat.subsingleton_of_isZero ht

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticFiniteSubfamilyTor

/-! ## 任意モニック族の実残余評価の Tor 消滅

## 概要

任意モニック族の有界深さ有限部分族図式の全段、および全評価源の高次 Tor は零。
BS 著者版 Remark 7.15（著者版 p.62）の任意族の実導来剰余計算。

## 方針

既存の有限部分族の Koszul 分解と実評価図式の余極限を使い、
同じ TorAlg 関手が有限部分集合図式の余極限を保つことを適用する。
原典の BS 著者版 Proposition 7.11 による証明とは異なる PD 計算の経路。

## 規約

添字型全体は任意。p 正則性と δ(d) の単元性を明示し、正次数を要求しない。
余極限の保存は既存の一般定理から供給し、外部仮定には残さない。

## 使われ方

実残余係数射に沿う全評価源の Tor 非輪状性を供給する。
-/

@[expose] public noncomputable section MonicPrismaticBoundedSupportTor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {σ : Type u}

private theorem coordinate_range {m : ℕ} (T : Finset σ) (s : Fin m ≃ T) (N : ℕ) :
    Set.range (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N).get =
      {z : σ × ℕ | z.1 ∈ T ∧ z.2 ≤ N} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, k, hk, he⟩ :=
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_mem (fun i => (s i : σ)) N _).mp (List.get_mem _ i)
    rw [← he]
    exact ⟨(s j).property, hk⟩
  · rintro ⟨hz, hn⟩
    obtain ⟨j, hj⟩ := s.surjective ⟨z.1, hz⟩
    have hm : z ∈ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N :=
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_mem (fun i => (s i : σ)) N z).mpr
        ⟨j, z.2, hn, Prod.ext (congrArg Subtype.val hj) rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    exact ⟨i, hi⟩

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "I" => Ideal.span {(p : L), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ" => RingHom.comp (Ideal.Quotient.mk I)
  (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
local notation "F" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E r
local notation "K" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal E r

/-- 概要：任意モニック族の有界深さ評価図式の全段の高次 Tor は零。
方針：有限座標の hull を選び、有限部分族の源グラフ商へ同定する。
規約：全添字型の有限性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実余極限の段ごとの入力。 -/
theorem monicPrismaticBoundedSupportStage_tor_subsingleton
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (S : Finset (σ × ℕ)) (i : ℕ) :
    Subsingleton (((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)).obj ((F).obj S)) := by
  classical
  let T := S.image Prod.fst
  let N := S.sup Prod.snd
  let s : Fin T.card ≃ T := (Finset.equivFin T).symm
  let cs := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (fun j => (s j : σ)) N
  have hcoords : Set.range cs.get = (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S : Set (σ × ℕ)) := by
    rw [coordinate_range T s N]
    ext z
    exact (_root_.SerrePositivity.BhattScholze.Andre.mem_deltaDivisionCoordinateHull S z).symm
  have hK : K (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S) =
      Ideal.span (Set.range fun j => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E r (cs.get j)) := by
    change Ideal.span (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E r ''
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S : Set (σ × ℕ))) = _
    rw [← hcoords, ← Set.range_comp']
  let e : (F).obj S ≅
      ModuleCat.of L (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E r cs.get) :=
    (Submodule.quotEquivOfEq _ _ (show (K (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S) : Submodule L L) =
      Ideal.span (Set.range fun j => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E r (cs.get j))
        from hK)).toModuleIso
  let H := (ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)
  have ht := monicPrismaticFiniteSubfamilySource_tor_subsingleton
    (T : Set σ) D d f s N hf hpA v hv i
  have hz : IsZero (H.obj
      (ModuleCat.of L (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E r cs.get))) := by
    let := ht
    exact ModuleCat.isZero_of_subsingleton _
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso (H.mapIso e))

/-- 概要：実図式の Tor 交換から、任意モニック族の全評価環の高次 Tor が消える。
方針：各段の消滅を余極限に移し、元の評価環との標準同型を使う。
規約：この中間補題の保存仮定は後の公開入口で解消する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全評価源。 -/
theorem monicPrismaticEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ)
    (hpres : PreservesColimit F ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := hpres
  let H := (ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)
  have hz : IsZero (H.obj (colimit F)) :=
    torAlg_finsetColimit_isZero_of_stages (σ × ℕ) ψ F (i + 1)
      (fun S => ModuleCat.isZero_iff_subsingleton.mpr
        (monicPrismaticBoundedSupportStage_tor_subsingleton D d f hf hpA v hv S i))
  let e : H.obj (ModuleCat.of L P) ≅ H.obj (colimit F) :=
    H.mapIso (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportColimitEvalIso E r).symm
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso e)


/-- 概要：任意モニック族の全評価環の高次 Tor は零。
方針：既存の TorAlg の有限部分集合余極限保存を実評価図式に適用する。
規約：余極限交換の追加仮定を残さない。正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の任意族の実残余係数拡大。 -/
theorem monicPrismaticEvaluation_tor_subsingleton
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  let := torAlg_preservesFinsetColimits (σ × ℕ) ψ (i + 1)
  exact monicPrismaticEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
    D d f hf hpA v hv i inferInstance

local notation "β" => deltaDivisionSourceEval E r
local notation "Mψ" => baseChangeScalarModule ψ
local notation "Mβ" => baseChangeScalarModule β

/-- 概要：任意モニック族の実残余係数加群は全 β 評価射に関して Tor 非輪状。
方針：全評価環の TorAlg 消滅を通常 Tor 比較と対称性で移す。
規約：族全体の有限性も余極限交換仮定も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準導来 augmentation による比較。 -/
theorem monicPrismaticBoundedSupportResidueEval_torVanishing
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    scalarExtensionTorVanishing β Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
    let := deltaDivisionSourceEvaluationAlgebra E r
    let : Subsingleton (((ModuleCat.extendScalars ψ).leftDerived (i + 1)).obj Mβ) :=
      monicPrismaticEvaluation_tor_subsingleton D d f hf hpA v hv i
    have hz : IsZero (((ModuleCat.extendScalars ψ).leftDerived (i + 1)).obj Mβ) :=
      ModuleCat.isZero_of_subsingleton _
    have hH := (derivedModuleBaseChangeHomologyIso ψ (i + 1)).app Mβ
    have hzH := hH.isZero_iff.mpr hz
    have hzR := (ModuleCat.restrictScalars ψ).map_isZero hzH
    have hzT := ((derivedModuleBaseChangeTorIso ψ (i + 1)).app Mβ).isZero_iff.mp hzR
    exact ((torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticBoundedSupportTor

/-! ## André 完全基底上の入力作用からの基底保存性

## 概要

完全基底上の有界入力 prism 間の射では、入力作用を保てば基底射も自動的に保たれる。
BS 著者版 Lemma 4.8（著者版 pp.38–39）の一意性を BS 著者版 Remark 7.15（p.62）の入力圏へ接続する。

## 方針

入力の可換性を係数環へ制限し、完全な基底から有界標的への prism 射の剛性を使う。
原典の変形理論とは異なる幾何和・イデアル冪による一意性の経路。

## 規約

対象は既に基底射を持つものとする。基底射の存在や絶対 site 全体との圏同値は主張しない。

## 使われ方

固定基底上の入力圏から基底射を省く比較における、射の条件の冗長性を解消する。
-/

@[expose] public noncomputable section BoundedPrismInputRigidity

namespace SerrePositivity.BhattScholze.Andre.BoundedPrismInput
open _root_.CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]
variable {W : OrientedPrism p A} {c : A ⧸ W.ideal →+* S}

/-- 概要：完全基底上の有界 prism 射は入力作用を保つなら基底も保つ。
方針：商射の基底制限を一致させ、一般有界標的での完全源の剛性を使う。
規約：標的の完全性・p 正則性は不要。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）と BS 著者版 Remark 7.15（p.62）の入力圏の比較。 -/
theorem prismHom_over_base_of_input (hW : W.deltaStructure.IsPerfect)
    (X Y : BoundedPrismInput W c) (f : OrientedPrism.Hom X.prism Y.prism)
    (hf : f.quotientMap.comp X.input = Y.input) : f.comp X.base = Y.base := by
  apply _root_.SerrePositivity.BhattScholze.perfectPrismHom_ext_to_bounded_target W hW Y.prism Y.bounded
  rw [OrientedPrism.Hom.quotientMap_comp, ← X.input_base,
    ← RingHom.comp_assoc, hf, Y.input_base]

/-- 概要：入力作用だけを保つ prism 射を入力圏の射へまとめる。
方針：完全基底に関する基底保存性を一意性から自動的に供給する。
規約：基底保存性を追加の引数として要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底を省く比較射の構成。 -/
def homOfInput (hW : W.deltaStructure.IsPerfect)
    (X Y : BoundedPrismInput W c) (f : OrientedPrism.Hom X.prism Y.prism)
    (hf : f.quotientMap.comp X.input = Y.input) : X ⟶ Y where
  toHom := f
  over_base := prismHom_over_base_of_input hW X Y f hf
  over_input := hf

/-- 概要：入力圏の射は、入力作用を保つ prism 射と型同値。
方針：台の prism 射への射影と基底保存性を自動供給する構成が互いに逆と示す。
規約：対象の基底射の存在は保持し、射の追加基底条件だけを除く。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）による絶対入力圏への比較の射の部分。 -/
def homEquivInputPreserving (hW : W.deltaStructure.IsPerfect)
    (X Y : BoundedPrismInput W c) :
    (X ⟶ Y) ≃ { f : OrientedPrism.Hom X.prism Y.prism //
      f.quotientMap.comp X.input = Y.input } where
  toFun f := ⟨f.toHom, f.over_input⟩
  invFun f := homOfInput hW X Y f.val f.property
  left_inv _f := hom_ext rfl
  right_inv _f := Subtype.ext rfl

end SerrePositivity.BhattScholze.Andre.BoundedPrismInput

end BoundedPrismInputRigidity

/-! ## 冪零核を持つ商に沿う忠実平坦性

## 概要

平坦な環射の可換四角形で、基底の商射が全射かつ核の各元が冪零なら、
商側の忠実平坦性から元の環射の忠実平坦性が従う。
BS 著者版 Remark 7.15（著者版 p.62）の ϖ 冪剰余の忠実性への一般環計算。

## 方針

全ての素イデアルが冪零核を含むため基底商から持ち上がり、
商側の忠実平坦性によるスペクトル全射性を可換四角形で戻す。

## 規約

核に一様な冪零指数を要求しない。完備性・Noether 性も不要。

## 使われ方

主元の冪による剰余の忠実平坦性を、第一剰余から得る。
-/

@[expose] public noncomputable section FaithfullyFlatNilpotentSquare

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：平坦な可換四角形の基底商が冪零核の全射なら、下辺の忠実平坦性は上辺へ戻る。
方針：素スペクトルの全射性を冪零核の基底商と下辺に沿って合成する。
規約：右辺の射は全射でなくてもよい。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の主冪剰余の忠実性。 -/
theorem faithfullyFlat_of_flat_of_nilpotent_square
    {R S B C : Type u} [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra B C] [Module.Flat R S] [Module.FaithfullyFlat B C]
    (qR : R →+* B) (qS : S →+* C) (hqR : Function.Surjective qR)
    (hnil : ∀ x ∈ RingHom.ker qR, IsNilpotent x)
    (hsq : qS.comp (algebraMap R S) = (algebraMap B C).comp qR) :
    Module.FaithfullyFlat R S := by
  apply Module.FaithfullyFlat.of_comap_surjective
  intro P
  have hker : RingHom.ker qR ≤ P.asIdeal := by
    intro x hx
    obtain ⟨n, hn⟩ := hnil x hx
    exact P.isPrime.mem_of_pow_mem n (hn.symm ▸ P.asIdeal.zero_mem)
  have hP : P ∈ Set.range (PrimeSpectrum.comap qR) := by
    rw [range_comap_of_surjective B qR hqR]
    exact hker
  obtain ⟨P', hP'⟩ := hP
  obtain ⟨Q', hQ'⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := B) (B := C) P'
  refine ⟨PrimeSpectrum.comap qS Q', ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, hsq, PrimeSpectrum.comap_comp_apply, hQ', hP']

end SerrePositivity.BhattScholze.Andre

end FaithfullyFlatNilpotentSquare

/-! ## 代数の主元完全忠実平坦性と正冪

## 概要

a 完全忠実平坦な可換代数は、全ての正冪 aⁿ に関しても完全忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の ϖ から p への移送に用いる。

## 方針

既存の冪ねじれ Tor 消滅から冪剰余の平坦性を得る。
第一剰余への全射の核が各元冪零であることを使い、剰余の忠実性も戻す。

## 規約

主元の正則性・完備性・Noether 性は不要。正冪指数を明示する。

## 使われ方

(ϖ^p)=(p) により自然な Hodge–Tate 候補の p 完全忠実平坦性を得る。
-/

@[expose] public noncomputable section CompletelyFaithfullyFlatPrincipalPower

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
attribute [local instance] adicQuotientAlgebra

/-- 概要：a 完全忠実平坦な代数の各正冪剰余は忠実平坦。
方針：冪剰余の平坦性と第一剰余への冪零核の可換四角形を使う。
規約：正則性も完備性も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の p 剰余の忠実性。 -/
theorem faithfullyFlat_power_algebraQuotient_of_completelyFaithfullyFlat
    {R : Type u} [CommRing R] (a : R) (S : Type u) [CommRing S] [Algebra R S]
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) S) (n : ℕ) (hn : 0 < n) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {a ^ n})
      (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {a ^ n})) := by
  let I : Ideal R := Ideal.span {a}
  let In : Ideal R := Ideal.span {a ^ n}
  let c := algebraMap R S
  let J := Ideal.map c I
  let Jn := Ideal.map c In
  have hle : In ≤ I := Ideal.span_le.mpr (by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.mem_span_singleton.mpr (dvd_pow_self a (Nat.ne_of_gt hn)))
  let qR : (R ⧸ In) →+* R ⧸ I := Ideal.Quotient.factor hle
  let qS : (S ⧸ Jn) →+* S ⧸ J := Ideal.Quotient.factor (Ideal.map_mono hle)
  let : Module.Flat (R ⧸ In) (S ⧸ Jn) :=
    flat_power_algebraQuotient_of_completelyFlat a S hS.1 n
  let : Module.FaithfullyFlat (R ⧸ I) ((R ⧸ I) ⊗[R] S) := hS.2
  let : Module.FaithfullyFlat (R ⧸ I) (S ⧸ J) :=
    Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) ((R ⧸ I) ⊗[R] S)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  apply faithfullyFlat_of_flat_of_nilpotent_square qR qS (Ideal.Quotient.factor_surjective hle)
  · intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hr
    refine ⟨n, ?_⟩
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hz, mul_pow]
    exact Ideal.mem_span_singleton.mpr ⟨z ^ n, rfl⟩
  · apply Ideal.Quotient.ringHom_ext
    ext r
    rfl

/-- 概要：主元完全忠実平坦性は全ての正冪に保存される。
方針：既存の完全平坦性の冪保存と、環商の忠実平坦性を剰余テンソルへ移す比較を結ぶ。
規約：可換代数を対象とし、正則性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の (ϖ^p)=(p) に沿う移送。 -/
theorem completelyFaithfullyFlat_principal_power_algebra
    {R : Type u} [CommRing R] (a : R) (S : Type u) [CommRing S] [Algebra R S]
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) S) (n : ℕ) (hn : 0 < n) :
    IsCompletelyFaithfullyFlat (Ideal.span {a ^ n}) S := by
  refine ⟨isCompletelyFlat_principal_power a S hS.1 n, ?_⟩
  let I : Ideal R := Ideal.span {a ^ n}
  let : Module.FaithfullyFlat (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I) :=
    faithfullyFlat_power_algebraQuotient_of_completelyFaithfullyFlat a S hS n hn
  exact Module.FaithfullyFlat.of_linearEquiv (R ⧸ I)
    (S ⧸ Ideal.map (algebraMap R S) I)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end CompletelyFaithfullyFlatPrincipalPower

/-! ## 根付き拡大の基底環同型による移送

## 概要

環同型は任意イデアルに関して完全忠実平坦であり、根付き p 完全忠実平坦拡大を
同じ宇宙の同型な基底環へ移せる。BS 著者版 Theorem 7.14（著者版 p.61）の構成の基底表示の比較。

## 方針

基底自身の完全忠実平坦性を線形同型で移し、既存の環射の合成定理を使う。
根方程式には多項式 map と eval₂ の自然性を用いる。
原典の BS 著者版 Proposition 7.11 による証明とは異なる、BS 著者版 Remark 7.15（p.62）に沿う構成の補助計算。

## 規約

環射の作用は全て toAlgebra で固定する。元と終域の台環は同じ Type u に置く。

## 使われ方

完全 prism 商上の結果を、その商表示を持つ元の perfectoid 基底へ移す。
-/

@[expose] public noncomputable section MonicRootedBaseEquiv

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open scoped _root_.TensorProduct
variable {R S T σ : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- 概要：基底自身は任意イデアルに関して完全忠実平坦。
方針：高次 Tor の消滅と剰余テンソルの右単位同型を使う。
規約：通常の自己スカラー作用を使う。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の基底環同型への移送。 -/
theorem monicRootedBase_self_isCompletelyFaithfullyFlat (I : Ideal R) :
    IsCompletelyFaithfullyFlat I R := by
  constructor
  · intro N _ _ _
    apply (isConcentratedInDegreeZero_derivedTensor_iff R N).mpr
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact torModule_subsingleton_of_flat R N m
  · exact Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) (R ⧸ I)
      (TensorProduct.AlgebraTensorModule.rid R (R ⧸ I) (R ⧸ I))

/-- 概要：環同型は任意イデアルに関して完全忠実平坦。
方針：環同型を元の環上の線形同型とみなし、自己拡大の性質を移す。
規約：終域の係数作用は同型の toAlgebra に固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的商表示からの移送。 -/
theorem monicRootedBase_equiv_isCompletelyFaithfullyFlat (e : R ≃+* S) (I : Ideal R) :
    letI := e.toRingHom.toAlgebra
    IsCompletelyFaithfullyFlat I S := by
  let := e.toRingHom.toAlgebra
  let E : R ≃ₗ[R] S :=
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        change e (a * x) = e a * e x
        exact e.map_mul a x }
  exact isCompletelyFaithfullyFlat_of_linearEquiv I E
    (monicRootedBase_self_isCompletelyFaithfullyFlat I)

/-- 概要：同型先の基底の根付き p 完全忠実平坦拡大は元の基底の拡大でもある。
方針：同型の完全忠実平坦性と環射の合成定理を使い、eval₂_map で根方程式を移す。
規約：多項式族の性質や有限性はこの移送には不要。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の基底表示の解消。 -/
theorem monicRootedExtension_of_baseEquiv (p : ℕ) [Fact p.Prime]
    (e : R ≃+* S) (f : σ → Polynomial R) (g : S →+* T) (ρ : σ → T)
    (hT : IsIntegralPerfectoid T p)
    (hflat : letI := g.toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : S)}) T)
    (hroot : ∀ s, ((f s).map e.toRingHom).eval₂ g (ρ s) = 0) :
    IsIntegralPerfectoid T p ∧
      (letI := (g.comp e.toRingHom).toAlgebra;
        IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ (g.comp e.toRingHom) (ρ s) = 0 := by
  refine ⟨hT, ?_, ?_⟩
  · exact Transfinite.isCompletelyFaithfullyFlat_natCast_comp e.toRingHom g p
      (monicRootedBase_equiv_isCompletelyFaithfullyFlat e _) hflat
  · intro s
    simpa only [Polynomial.eval₂_map] using hroot s

end SerrePositivity.BhattScholze.Andre

end MonicRootedBaseEquiv

/-! ## 任意の整 perfectoid 基底上の有限モニック根付き拡大

## 概要

任意の整 perfectoid 環上の有限正次数モニック族には、全ての多項式の根を持つ
p 完全忠実平坦な整 perfectoid 拡大がある。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の一段の有限版。

## 方針

非零枝では Fontaine 写像の核の実 PD 完備化から完全 prism 商表示を得る。
商表示へ多項式を移して有限族の構成を適用し、環同型に沿って基底作用と根を戻す。
零枝は自己拡大を使う。原典の BS 著者版 Proposition 7.11 による証明とは異なる PD 計算の経路である。

## 規約

各多項式に正次数を要求する。有限性以外に基底の表示・p 正則性・ねじれなしを仮定しない。

## 使われ方

任意族への有向余極限と p 完備化を構成する前の一元・有限族の存在結果。
-/

@[expose] public noncomputable section FiniteMonicRootedExtension

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.DerivedCompletion

/-- 概要：任意の整 perfectoid 基底上の有限正次数モニック族に、全根を持つ拡大がある。
方針：完全 prism 商表示で有限族を構成し、基底環同型と評価の自然性で戻す。
規約：全列挙以外に補助的な忠実平坦性や基底表示を仮定しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の一段構成の有限版。 -/
theorem exists_finiteMonicRootedPerfectoidExtension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    {σ : Type u} (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) {m : ℕ} (eσ : Fin m ≃ σ) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  rcases hR with hs | ⟨hp, hc, ⟨π, v, hv⟩, hF, hker⟩
  · let := hs
    refine ⟨R, inferInstance, RingHom.id R, fun _ => 0, Or.inl hs, ?_, ?_⟩
    · exact monicRootedBase_self_isCompletelyFaithfullyFlat _
    · intro s
      exact Subsingleton.elim _ _
  · let := hc
    let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    obtain ⟨d, hd, e, _⟩ := exists_perfectoidTrialPrism R p hF hker π v hv
    let := pdCompletionCommRing (WittVector p (PreTilt R p)) p d
    let P := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    have hP := perfectDeltaPDPrism_isPerfect (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    let F := fun s => (f s).map e.symm.toRingHom
    have hFm : ∀ s, (F s).Monic := fun s => (hf s).map _
    have hFd : ∀ s, 0 < (F s).natDegree := by
      intro s
      rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective]
      exact hdeg s
    obtain ⟨T, hT, g, ρ, hperf, hflat, hroot⟩ :=
      exists_finiteMonicRootedPerfectoidExtension_of_perfectPrism P hP F hFm hFd eσ
    let := hT
    exact ⟨T, hT, g.comp e.symm.toRingHom, ρ,
      monicRootedExtension_of_baseEquiv p e.symm f g ρ hperf hflat hroot⟩

/-- 概要：有限添字型で与えられた正次数モニック族に同じ根付き拡大が存在する。
方針：Fin による全列挙を選び、一般基底上の有限族構成を適用する。
規約：有限性は命題の型クラスで与え、根の添字型は元のままに保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の任意有限部分族の根添加。 -/
theorem exists_monicRootedPerfectoidExtension_of_finite
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    {σ : Type u} [Finite σ] (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  let := Fintype.ofFinite σ
  exact exists_finiteMonicRootedPerfectoidExtension R p hR f hf hdeg (Fintype.equivFin σ).symm

/-- 概要：任意の整 perfectoid 環上の正次数モニック多項式に、根を持つ拡大がある。
方針：一元族に一般基底上の有限族の存在定理を適用する。
規約：基底環への追加条件を課さず、同じ p に関する完全忠実平坦性を結論する。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の一元根添加。 -/
theorem exists_monicRootPerfectoidExtension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : Polynomial R) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      f.eval₂ φ ρ = 0 := by
  obtain ⟨T, hT, φ, ρ, hperf, hflat, hroot⟩ :=
    exists_monicRootedPerfectoidExtension_of_finite R p hR
      (fun _ : PUnit.{u + 1} => f) (fun _ => hf) (fun _ => hdeg)
  exact ⟨T, hT, φ, ρ PUnit.unit, hperf, hflat, hroot PUnit.unit⟩

end SerrePositivity.BhattScholze.Andre

end FiniteMonicRootedExtension

/-! ## モニック族の raw Frobenius 除算の初期係数商

## 概要

任意のモニック族の raw φ/p 包の初期係数商を、mod p における関係の p 乗の通常商として表示する。
正次数モニック族ならこの係数商は A/p 上忠実平坦。
BS 著者版 Corollary 2.39（p.25）、BS 著者版 Remark 7.15(1)（p.62）の実剰余計算の一部である。

## 方針

一般 δ 除算の初期イデアルの Frobenius・冪比較と、全族の係数商の交換同型を合成する。
前工程の任意モニック族の通常忠実平坦性を標準係数射に沿って移す。

## 規約

同型自体にはモニック性・正次数・p 正則性を要求しない。
忠実平坦性にはモニック性と正次数を要求する。raw 包全体や完備化後の平坦性は別工程。

## 使われ方

一般 δ 除算の raw mod p 商の忠実平坦性を元の A/p に対して供給する。
-/

@[expose] public noncomputable section MonicFrobeniusCoefficient

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun s : σ => monicRelation (f s) s)
local notation "a" => (fun s : σ => DeltaStructure.frobeniusLift E (r s))
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "J" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal (p := p) (p : P) a
local notation "g" => (fun s : σ => Polynomial.map q (f s ^ p))
local notation "C" => PolynomialFamilyQuotient g

/-- 概要：モニック関係族の raw φ/p 包の初期係数商。
方針：既存 δ 除算の初期係数イデアルの商をそのまま使う。
規約：関係式のモニック性は定義に含めない。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実 mod p 表示の係数環。 -/
abbrev MonicFrobeniusCoefficientQuotient := P ⧸ J

/-- 概要：初期係数イデアルは p の係数拡張と関係多項式の p 乗のイデアルの和。
方針：Frobenius と p 乗の初期イデアル比較、および評価と冪の可換性を使う。
規約：任意多項式族に成立する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の係数商を通常モニック商へ移す。 -/
theorem monicFrobeniusCoefficientIdeal_eq :
    J = (I).map (MvPolynomial.C : A →+* P) ⊔ polynomialFamilyRelationIdeal (fun s => f s ^ p) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionFirstBaseIdeal_frobenius_eq_power]
  unfold _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstBaseIdeal
  have hpp : Ideal.span {(p : P), (p : P)} = Ideal.span {(p : P)} :=
    congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : P)))
  rw [hpp]
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  congr 1
  unfold polynomialFamilyRelationIdeal
  congr 1
  congr 1
  funext s
  exact (Polynomial.eval₂_pow _ _ p).symm

/-- 概要：raw 初期係数商は mod p の多項式の p 乗の通常商に同型。
方針：初期イデアルの表示と全族の係数商の交換同型を合成する。
規約：この同型は任意族に対して定義する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実剰余の通常忠実平坦性。 -/
def monicFrobeniusCoefficientEquiv : MonicFrobeniusCoefficientQuotient D f ≃+* C :=
  (Ideal.quotEquivOfEq (monicFrobeniusCoefficientIdeal_eq D f)).trans
    (polynomialFamilyBaseQuotientEquiv I (fun s => f s ^ p))

/-- 概要：係数商同型は多項式の係数を mod p に写す。
方針：商イデアル同定と係数商同型の代表元公式を使う。
規約：元の変数は保持する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実係数作用の比較。 -/
theorem monicFrobeniusCoefficientEquiv_mk (x : P) :
    monicFrobeniusCoefficientEquiv D f (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk (polynomialFamilyRelationIdeal g) (MvPolynomial.map q x) := by
  rw [monicFrobeniusCoefficientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    polynomialFamilyBaseQuotientEquiv_mk]

/-- 概要：表示同型は元の係数の標準像を A/p の通常係数作用に対応させる。
方針：代表元公式に定数多項式を代入する。
規約：元の A の任意元で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数環への平坦性移送。 -/
theorem monicFrobeniusCoefficientEquiv_C (x : A) :
    monicFrobeniusCoefficientEquiv D f (Ideal.Quotient.mk J (MvPolynomial.C x)) =
      algebraMap QA C (q x) := by
  rw [monicFrobeniusCoefficientEquiv_mk, MvPolynomial.map_C]
  rfl

/-- 概要：初期係数商への標準 A/p 係数射。
方針：通常商への係数射を表示同型の逆で戻す。
規約：次の代表元公式で自然な係数射に一致することを確認する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実係数商の代数構造。 -/
def monicFrobeniusCoefficientBaseMap : QA →+* MonicFrobeniusCoefficientQuotient D f :=
  (monicFrobeniusCoefficientEquiv D f).symm.toRingHom.comp (algebraMap QA C)

/-- 概要：標準 A/p 係数射は元の A 係数の自然な商像で与えられる。
方針：表示同型を適用して元の係数像を比較する。
規約：環射の定義だけでなく代表元での等式を保証する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 商の係数作用。 -/
theorem monicFrobeniusCoefficientBaseMap_mk (x : A) :
    monicFrobeniusCoefficientBaseMap D f (q x) = Ideal.Quotient.mk J (MvPolynomial.C x) := by
  apply (monicFrobeniusCoefficientEquiv D f).injective
  change (monicFrobeniusCoefficientEquiv D f)
    ((monicFrobeniusCoefficientEquiv D f).symm _) = _
  rw [RingEquiv.apply_symm_apply, monicFrobeniusCoefficientEquiv_C]

/-- 概要：標準係数射による初期係数商の A/p 代数構造。
方針：明示した環射の toAlgebra を用いる。
規約：利用箇所で局所的に導入する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の係数商の忠実平坦性。 -/
@[instance_reducible] def monicFrobeniusCoefficientBaseAlgebra :
    Algebra QA (MonicFrobeniusCoefficientQuotient D f) :=
  (monicFrobeniusCoefficientBaseMap D f).toAlgebra

/-- 概要：初期係数商の表示は標準 A/p 係数作用に関する代数同型。
方針：表示同型の逆で定義した係数射との可換性を使う。
規約：元の A/p スカラーを変えない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の忠実平坦性の移送。 -/
def monicFrobeniusCoefficientAlgEquiv :
    letI := monicFrobeniusCoefficientBaseAlgebra D f
    MonicFrobeniusCoefficientQuotient D f ≃ₐ[QA] C := by
  let := monicFrobeniusCoefficientBaseAlgebra D f
  apply AlgEquiv.ofRingEquiv (f := monicFrobeniusCoefficientEquiv D f)
  intro x
  exact (monicFrobeniusCoefficientEquiv D f).apply_symm_apply _

/-- 概要：正次数モニック族の raw 初期係数商は A/p 上忠実平坦。
方針：mod p の非零係数環ではモニック性と次数を保つ係数変更を使い、
通常の任意モニック族商の忠実平坦性を移す。零係数商は加群の自明性で処理する。
規約：A の p 正則性も族の有限性も不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の raw 実 mod p 商の忠実平坦性の係数入力。 -/
theorem monicFrobeniusCoefficient_faithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicFrobeniusCoefficientBaseAlgebra D f
    Module.FaithfullyFlat QA (MonicFrobeniusCoefficientQuotient D f) := by
  let := monicFrobeniusCoefficientBaseAlgebra D f
  have hc : Module.FaithfullyFlat QA C := by
    rcases subsingleton_or_nontrivial QA with hs | hn
    · let := hs
      let : Subsingleton C := Module.subsingleton QA C
      rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
      refine ⟨inferInstance, ?_⟩
      intro N _ _ _
      exact Module.subsingleton QA N
    · let := hn
      apply polynomialFamilyQuotient_faithfullyFlat g
      · intro s
        exact ((hf s).pow p).map q
      · intro s
        rw [((hf s).pow p).natDegree_map, (hf s).natDegree_pow]
        exact Nat.mul_pos (Fact.out : p.Prime).pos (hdeg s)
  let := hc
  exact Module.FaithfullyFlat.of_linearEquiv QA C
    (monicFrobeniusCoefficientAlgEquiv D f).toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end MonicFrobeniusCoefficient
