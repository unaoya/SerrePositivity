module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootInput
public import SerrePositivity.BhattScholze.Andre.Variants.Auxiliary
public import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaLocalization
public import Mathlib.RingTheory.Flat.Localization
public import SerrePositivity.HomologicalAlgebra.TorBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import Mathlib.RingTheory.Localization.BaseChange
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.MvPolynomial.Localization
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationIso
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import SerrePositivity.HomologicalAlgebra.ScalarConeModuleQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.FaithfullyFlatDerivedHomology
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Tower
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection

/-!
# 係数局所化と分母冪ねじれ（正則性の仮定を外すための補題）

## 概要
完備化と冪ねじれによる負次数消滅の検出、自由係数代数の導来商正方形、源作用・評価因子の係数局所化、スカラー錐、単元分母での δ 射の可逆性と純性、安定局所化の核と分母冪ねじれ、p 錐、分子に 1 を含む raw 包の p 正則性、raw 除算包上の Frobenius 成分の合成。
BS 著者版 Remark 7.15 の係数比較に使う、局所化の分母と冪ねじれを扱う。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/Unconditional/RawRegular`、`PowerRootEnvelope/Unconditional/Residue`、`PowerRootEnvelope/Unconditional/Source`、`Variants/MonicRootedExtension`。
-/

universe u v w

/-! ## raw 除算包上での Frobenius 成分の合成

## 概要

無限根入力の raw 除算包に、係数 Frobenius と指数 Frobenius を別々に作用させる。
両比較射の合成は、合成自己同型が誘導する raw 射と一致する。
BS 著者版 Remark 7.15（著者版 p.62）の φ_A 係数変更と全体 Frobenius の関係。

## 方針

両成分の δ 互換性を raw 係数自己同型の一般構成へ供給し、合成の一般補題を適用する。

## 規約

未完備の環を扱う。係数成分は根変数を固定し、指数成分は係数を固定する。

## 使われ方

Frobenius による剰余比較と原典の係数引戻しを、変数の再配置を記録して結ぶ。
-/

@[expose] public noncomputable section PowerRootDivisionFrobeniusFactors

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
variable (D : DeltaStructure p A) (hD : D.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hD.p_mul_injective D
local notation "C" => powerRootCoefficientFrobeniusEquiv p D hD
local notation "V" => powerRootVariableFrobeniusEquiv (A := A) p
local notation "hC" => powerRootCoefficientFrobeniusEquiv_isDeltaHom p D hD
local notation "hV" => powerRootVariableFrobeniusEquiv_isDeltaHom p D hD
variable {σ : Type v}
variable (d : _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p (Nat.Prime.pos (Fact.out : p.Prime)))
variable (a : σ → _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p (Nat.Prime.pos (Fact.out : p.Prime)))

/-- 概要：係数 Frobenius のみを適用する raw 除算包の同型。
方針：係数成分の δ 自己同型を一般の raw 比較に渡す。
規約：入力族と分母の係数だけを送る。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の φ_A 係数変更の代数的部分。 -/
def powerRootCoefficientDivisionFrobeniusEquiv :
    DeltaAdjoinDivision E d a ≃+* DeltaAdjoinDivision E (C d) (fun s => C (a s)) :=
  deltaDivisionCoefficientAutEquiv E C hC d a

/-- 概要：指数 p 倍のみを適用する raw 除算包の同型。
方針：指数成分の δ 自己同型を一般の raw 比較に渡す。
規約：入力の係数環 A を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典の係数引戻しと変数作用の分離。 -/
def powerRootVariableDivisionFrobeniusEquiv :
    DeltaAdjoinDivision E d a ≃+* DeltaAdjoinDivision E (V d) (fun s => V (a s)) :=
  deltaDivisionCoefficientAutEquiv E V hV d a

/-- 概要：係数成分の後に指数成分を適用した raw 射は合成自己同型の raw 射。
方針：一般の係数自己同型比較の合成則を実無限根入力へ適用する。
規約：全体 Frobenius が二成分の合成であることは前ファイルの計算公式で固定済み。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 包における二つの Frobenius の比較。 -/
theorem powerRootDivisionFrobeniusFactors_comp :
    (powerRootVariableDivisionFrobeniusEquiv p D hD (C d) (fun s => C (a s))).toRingHom.comp
      (powerRootCoefficientDivisionFrobeniusEquiv p D hD d a).toRingHom =
    (deltaDivisionCoefficientAutEquiv E ((C).trans V) ((hV).comp hC) d a).toRingHom :=
  deltaDivisionCoefficientAutMap_trans E C V hC hV d a

end SerrePositivity.BhattScholze.Andre

end PowerRootDivisionFrobeniusFactors

/-! ## 自由な係数代数の実導来商正方形

## 概要
元の係数環 A 上自由な代数 S に対し、S 上の実導来対象の A/(I) 還元と
S/(IS) 還元の係数制限を比較する。

## 方針
射影加群の分裂表示を自由な係数制限で保ち、通常商の自然同型を射影モデルへ適用する。

## 規約
自由性は一般補題の明示的 instance であり、無限根自由 δ 源への適用では内部で供給する。

## 使われ方
BS 著者版 Remark 7.15（著者版 p.62）の元の A 作用を保つ無条件の導来剰余比較。
-/

@[expose] public noncomputable section FreeCoefficientSquare

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] [Module.Free A S]
local notation "L₀" => S
local notation "C₀" => algebraMap A S

/-- 自由な係数代数上の射影加群は、二重係数包含に沿う実係数制限でも射影的。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
theorem freeCoefficientRestrict_projective (M : ModuleCat.{u} L₀) [Projective M] :
    Projective ((ModuleCat.restrictScalars C₀).obj M) := by
  have : Module.Projective L₀ M := inferInstance
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := L₀) (P := M)).mp inferInstance
  let F := ModuleCat.restrictScalars C₀
  let Y := ModuleCat.of L₀ (M →₀ L₀)
  let i : M ⟶ Y := ModuleCat.ofHom s
  let r : Y ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination L₀ id)
  have hir : i ≫ r = 𝟙 M := ModuleCat.hom_ext hs
  let e : F.obj Y ≃ₗ[A] (M →₀ L₀) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (M →₀ L₀) at x
        apply Finsupp.ext
        intro m
        change (algebraMap A L₀ r) * x m = r • x m
        rw [Algebra.smul_def] }
  have : Module.Projective A (F.obj Y) := Module.Projective.of_equiv e.symm
  have hM : Module.Projective A (F.obj M) :=
    Module.Projective.of_split (F.map i).hom (F.map r).hom (by
      apply ModuleCat.hom_ext_iff.mp
      change F.map i ≫ F.map r = 𝟙 (F.obj M)
      rw [← F.map_comp, hir, F.map_id])
  exact ModuleCat.projective_of_categoryTheory_projective (F.obj M)

/-- 指定した実源射影モデルを、実A係数制限対象の射影モデルへ変換する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientModel
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    BoundedAboveDerivedModel (((boundedAboveDerivedRestrictScalars C₀).obj X).obj) where
  complex := ((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj P.complex
  bound := P.bound
  bounded := inferInstance
  projective i := freeCoefficientRestrict_projective (P.complex.X i)
  iso := (boundedAboveDerivedRestrictScalarsModelIso C₀ X P).symm

/-- 元の係数環の任意イデアルでの実導来還元を、制限した具体的射影モデルで計算する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientQuotientModelIso (I : Ideal A)
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X)).obj ≅
      DerivedCategory.Q.obj (baseChange (Ideal.Quotient.mk I)
        (((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj P.complex)) :=
  boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk I) _
    (freeCoefficientModel X P)


variable (I : Ideal A)
local notation "J₀" => Ideal.map C₀ I
local notation "κ₀" => algebraMap (A ⧸ I) (L₀ ⧸ J₀)
attribute [local instance] adicQuotientAlgebra

omit [Module.Free A S] in
/-- 自由な係数代数の拡張イデアルによる作用部分加群は、元の係数イデアルの作用に一致する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
theorem freeCoefficientIdeal_smul_restrict (M : ModuleCat.{u} L₀) :
    letI := Module.compHom M C₀
    letI : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    (J₀ • (⊤ : Submodule L₀ M)).restrictScalars A = I • (⊤ : Submodule A M) := by
  let := Module.compHom M C₀
  let : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Submodule.restrictScalars_map_smul_eq I ⊤

/-- Aへ制限してから係数商を取る操作と、Lで拡張イデアルの商を取る操作の標準同型。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientQuotientModuleIso (M : ModuleCat.{u} L₀) :
    (quotientModuleFunctor I).obj ((ModuleCat.restrictScalars C₀).obj M) ≅
      (ModuleCat.restrictScalars κ₀).obj ((quotientModuleFunctor J₀).obj M) := by
  letI := Module.compHom M C₀
  letI : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA := (Submodule.quotEquivOfEq _ _
    (freeCoefficientIdeal_smul_restrict I M).symm).trans
      (Submodule.Quotient.restrictScalarsEquiv A (J₀ • (⊤ : Submodule L₀ M)))
  refine ModuleCat.isoMk eA.toAddEquiv.toAddCommGrpIso ?_
  intro s
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
  ext x
  exact (eA.map_smul a x).symm

/-- 標準商像を保つ通常係数商比較の公式。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
theorem freeCoefficientQuotientModuleIso_mk (M : ModuleCat.{u} L₀) (x : M) :
    (freeCoefficientQuotientModuleIso I M).hom
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  rfl

/-- この係数商比較は実源加群の任意の射に自然。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientQuotientModuleNatIso :
    ModuleCat.restrictScalars C₀ ⋙ quotientModuleFunctor I ≅
      quotientModuleFunctor J₀ ⋙ ModuleCat.restrictScalars κ₀ := by
  refine NatIso.ofComponents (freeCoefficientQuotientModuleIso I) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change (freeCoefficientQuotientModuleIso I N).hom
        (Submodule.Quotient.mk (f.hom x)) =
          ((ModuleCat.restrictScalars κ₀).map ((quotientModuleFunctor J₀).map f))
            ((freeCoefficientQuotientModuleIso I M).hom (Submodule.Quotient.mk x))
      rw [freeCoefficientQuotientModuleIso_mk,
        freeCoefficientQuotientModuleIso_mk]
      rfl

/-- 同じ通常商比較を、実際の通常係数拡大関手の自然同型として表す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientScalarExtensionNatIso :
    ModuleCat.restrictScalars C₀ ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I) ≅
      ModuleCat.extendScalars (Ideal.Quotient.mk J₀) ⋙ ModuleCat.restrictScalars κ₀ :=
  Functor.isoWhiskerLeft _ (quotientScalarExtensionIso I) ≪≫
    freeCoefficientQuotientModuleNatIso I ≪≫
      Functor.isoWhiskerRight (quotientScalarExtensionIso J₀).symm _

/-- 実源の任意の複体について、通常の係数商比較を項ごとに適用する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientCochainSquareIso
    (K : CochainComplex (ModuleCat.{u} L₀) ℤ) :
    baseChange (Ideal.Quotient.mk I)
        (((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj K) ≅
      ((ModuleCat.restrictScalars κ₀).mapHomologicalComplex (.up ℤ)).obj
        (baseChange (Ideal.Quotient.mk J₀) K) :=
  (Functor.mapHomologicalComplexCompIso
    (freeCoefficientScalarExtensionNatIso I) (.up ℤ)).app K

attribute [local instance] HasDerivedCategory.standard

/-- 元の係数商への実導来還元は、実源商での還元を係数制限した対象と同型。
具体的係数代数のA自由性から制限射影モデルを供給し、Tor仮定は追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientDerivedSquareIso
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J₀)).obj X) :=
  ObjectProperty.isoMk _
    (freeCoefficientQuotientModelIso I X P ≪≫
      DerivedCategory.Q.mapIso (freeCoefficientCochainSquareIso I P.complex) ≪≫
        ((derivedRestrictScalarsFactors κ₀).app
          (baseChange (Ideal.Quotient.mk J₀) P.complex)).symm ≪≫
        (derivedRestrictScalars κ₀).mapIso
          (boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk J₀) X P).symm)


end SerrePositivity.BhattScholze.Andre

end FreeCoefficientSquare

/-! ## 分子に 1 を含む元の raw δ 包の p 正則性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の次数零モニック入力では、元の raw 包も p 正則。

## 方針
除算関係から分母を単元にし、Frobenius 安定局所化へ写す実 δ 射の単射性を普遍性で示す。

## 規約
元の raw δ 閉包商を保つ。ねじれ除去・完備化は行わない。

## 使われ方
正次数入力の結果と合わせ、元の raw p 正則性から hpR を完全に除く。
-/

@[expose] public noncomputable section UnitNumeratorRawRegular

namespace SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "Raw" => DeltaAdjoinDivision D d a
local notation "j" => deltaAdjoinDivisionMap D d a
local notation "DRaw" => deltaAdjoinDivisionStructure D d a

/-- 概要：分子族に 1 があれば、元の raw 包で分母の標準像は単元。
方針：元の除算変数を逆元として使う。
規約：分母の正則性や p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の次数零入力。 -/
theorem unconditionalRaw_denominator_isUnit_of_unit_numerator (ha : ∃ s, a s = 1) :
    IsUnit (j d) := by
  obtain ⟨s, hs⟩ := ha
  have hv : j d * deltaAdjoinDivisionVariable D d a s = 1 := by
    rw [deltaAdjoinDivision_relation, hs, map_one]
  exact ⟨⟨j d, deltaAdjoinDivisionVariable D d a s, hv, (mul_comm _ _).trans hv⟩, rfl⟩

/-- 概要：分子族に 1 があれば、元の raw 包の p 正則性は係数環から従う。
方針：実安定局所化への δ 射に左逆を作り、局所化の p 正則性を元の raw 包へ戻す。
規約：prism 商の正則性を要求せず、元の raw 包を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の次数零モニック入力の p 正則性。 -/
theorem unconditionalRaw_prime_regular_of_unit_numerator
    (hp : IsSMulRegular A (p : A)) (ha : ∃ s, a s = 1) :
    IsSMulRegular Raw (p : Raw) := by
  let T := D.frobeniusDenominators (Submonoid.powers d)
  let B := Localization T
  let DB := D.localization T B (D.frobeniusDenominators_stable (Submonoid.powers d))
  have hdB : IsUnit (algebraMap A B d) := IsLocalization.map_units B
    ⟨d, D.le_frobeniusDenominators (Submonoid.powers d) (Submonoid.mem_powers d)⟩
  have hdRaw := unconditionalRaw_denominator_isUnit_of_unit_numerator D d a ha
  have hj : D.IsDeltaHom DRaw j := deltaAdjoinDivisionMap_isDeltaHom D d a
  obtain ⟨f, hf, _⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D DB d a
    (algebraMap A B)
    (D.isDeltaHom_localization T B (D.frobeniusDenominators_stable (Submonoid.powers d)))
    hdB.mul_right_injective (fun s => hdB.dvd)
  have hM (s : Submonoid.powers d) : IsUnit (j s) := by
    obtain ⟨n, hn⟩ := s.property
    rw [← hn, map_pow]
    exact hdRaw.pow n
  obtain ⟨g, hg, _⟩ := D.existsUnique_saturatedLocalization_lift (Submonoid.powers d)
    B DRaw j hj hM
  obtain ⟨_, _, hu⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D DRaw d a j hj
    hdRaw.mul_right_injective (fun s => hdRaw.dvd)
  have hbase : (g.comp f).comp j = j := by
    rw [RingHom.comp_assoc, hf.2, hg.1]
  have hgf : g.comp f = RingHom.id Raw :=
    (hu _ ⟨hg.2.comp hf.1, hbase⟩).trans
      (hu _ ⟨fun _ => rfl, RingHom.id_comp j⟩).symm
  have hfi : Function.Injective f :=
    (show Function.LeftInverse g f from fun x => DFunLike.congr_fun hgf x).injective
  letI : Module.Flat A B := IsLocalization.flat B T
  have hpB : IsSMulRegular B (p : B) := by
    simpa only [map_natCast] using hp.of_flat (S := B)
  intro x y hxy
  apply hfi
  apply hpB
  change (p : B) * f x = (p : B) * f y
  simpa only [smul_eq_mul, map_mul, map_natCast] using congrArg f hxy

end SerrePositivity.BhattScholze.Andre

end UnitNumeratorRawRegular

/-! ## 係数を固定する実源作用の局所化

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の実源の右因子を係数局所化へ運ぶ。

## 方針
分母集合を固定する環自己射による加群作用について、元の局所化射が加群局所化になる。

## 規約
元の係数射と作用を保持し、自己射の可逆性は要求しない。

## 使われ方
元の二因子導来源と局所化先の二因子源との比較に用いる。
-/

@[expose] public noncomputable section LocalizedScalarModule

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (α : R →+* R) (β : S →+* S)
variable (hcomm : β.comp (algebraMap R S) = (algebraMap R S).comp α)

/-- 概要：可換な自己射を持つ局所化射を、元の自己射作用間の線形射として表す。
方針：環射の可換性をスカラー作用の可換性へ書き直す。
規約：台写像は元の標準係数射。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の右因子の比較。 -/
def unconditionalScalarModuleCoefficientMap :
    baseChangeScalarModule α →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj (baseChangeScalarModule β) where
  toFun := algebraMap R S
  map_add' := map_add _
  map_smul' r x := by
    change R at x
    change algebraMap R S (α r * x) = β (algebraMap R S r) * algebraMap R S x
    rw [map_mul, show β (algebraMap R S r) = algebraMap R S (α r) from
      DFunLike.congr_fun hcomm r]

/-- 概要：分母集合を固定する自己射の係数加群も、元の局所化射で局所化される。
方針：通常局所化の単元性・分数表示・核判定を元の作用へ移す。
規約：自己射の単射性・平坦性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実源右因子の係数拡大。 -/
theorem unconditionalScalarModuleCoefficientMap_isLocalizedModule
    (M : Submonoid R) [IsLocalization M S] (hfix : ∀ s : M, α s = s) :
    IsLocalizedModule M (unconditionalScalarModuleCoefficientMap α β hcomm) where
  map_units := by
    intro s
    apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun x : S => β (algebraMap R S s) * x)
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp ((IsLocalization.map_units S s).map β)
  surj y := by
    change S at y
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj M y
    refine ⟨(x, s), ?_⟩
    change β (algebraMap R S s) * y = algebraMap R S x
    rw [show β (algebraMap R S s) = algebraMap R S (α s) from
      DFunLike.congr_fun hcomm (s : R), hfix]
    exact (mul_comm _ _).trans hs
  exists_of_eq := by
    intro x y hxy
    change R at x y
    change algebraMap R S x = algebraMap R S y at hxy
    obtain ⟨s, hs⟩ := IsLocalization.eq_iff_exists M S |>.mp hxy
    refine ⟨s, ?_⟩
    change α s * x = α s * y
    rw [hfix]
    exact hs

/-- 概要：自己射で作用する元の加群の係数拡大は、局所化先の自己射係数加群。
方針：元の係数射の加群局所化性を通常テンソルの普遍性へ移す。
規約：元の自己射作用と標準係数拡大を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二因子源の右因子の実比較。 -/
def unconditionalScalarModuleLocalizationEquiv
    (M : Submonoid R) [IsLocalization M S] (hfix : ∀ s : M, α s = s) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (baseChangeScalarModule α) ≃ₗ[S]
      baseChangeScalarModule β := by
  let N := (ModuleCat.restrictScalars (algebraMap R S)).obj (baseChangeScalarModule β)
  letI : Module S N := Module.compHom S β
  letI : IsScalarTower R S N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let f := unconditionalScalarModuleCoefficientMap α β hcomm
  have : IsLocalizedModule M f :=
    unconditionalScalarModuleCoefficientMap_isLocalizedModule α β hcomm M hfix
  let h := IsLocalizedModule.isBaseChange M S f
  exact (extendScalarsObjEquivTensor R S (baseChangeScalarModule α)).trans h.equiv

end SerrePositivity.BhattScholze.Andre

end LocalizedScalarModule

/-! ## 実評価因子の係数局所化

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の実源の左評価因子を係数局所化へ運ぶ。

## 方針
可換な環射の正方形について、分母像での局所化を加群局所化として比較する。

## 規約
評価射の単射性・平坦性を要求せず、元の標準係数射を保つ。

## 使われ方
元の二因子導来源と局所化先の二因子源との比較に用いる。
-/

@[expose] public noncomputable section LocalizedEvaluationModule

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
variable [Algebra R S] [Algebra T U]
variable (φ : R →+* T) (ψ : S →+* U)
variable (hcomm : ψ.comp (algebraMap R S) = (algebraMap T U).comp φ)

/-- 概要：可換な環射の正方形の係数射を、評価作用を保つ線形射にする。
方針：正方形の可換性をスカラー作用へ適用する。
規約：台写像は元の標準係数射。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の左評価因子の局所化。 -/
def unconditionalEvaluationCoefficientMap :
    baseChangeScalarModule φ →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj (baseChangeScalarModule ψ) where
  toFun := algebraMap T U
  map_add' := map_add _
  map_smul' r x := by
    change T at x
    change algebraMap T U (φ r * x) = ψ (algebraMap R S r) * algebraMap T U x
    rw [map_mul, show ψ (algebraMap R S r) = algebraMap T U (φ r) from
      DFunLike.congr_fun hcomm r]

/-- 概要：分母像で局所化した評価環への係数射は、元の評価加群の局所化。
方針：実局所化の分数表示と核判定を分母像の代表元に沿って移す。
規約：評価環自体の元の作用を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の左因子の通常係数拡大比較。 -/
theorem unconditionalEvaluationCoefficientMap_isLocalizedModule
    (M : Submonoid R) [IsLocalization M S] [IsLocalization (M.map φ.toMonoidHom) U] :
    IsLocalizedModule M (unconditionalEvaluationCoefficientMap φ ψ hcomm) where
  map_units := by
    intro s
    apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun x : U => ψ (algebraMap R S s) * x)
    rw [show ψ (algebraMap R S s) = algebraMap T U (φ s) from
      DFunLike.congr_fun hcomm (s : R)]
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp
      (IsLocalization.map_units (M := M.map φ.toMonoidHom) U
        ⟨φ s, ⟨s, s.property, rfl⟩⟩)
  surj y := by
    change U at y
    obtain ⟨⟨x, t⟩, ht⟩ := IsLocalization.surj (M.map φ.toMonoidHom) y
    obtain ⟨s, hs, hst⟩ := t.property
    change φ s = (t : T) at hst
    refine ⟨(x, ⟨s, hs⟩), ?_⟩
    change ψ (algebraMap R S s) * y = algebraMap T U x
    rw [show ψ (algebraMap R S s) = algebraMap T U (φ s) from
      DFunLike.congr_fun hcomm s, hst]
    exact (mul_comm _ _).trans ht
  exists_of_eq := by
    intro x y hxy
    change T at x y
    change algebraMap T U x = algebraMap T U y at hxy
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists (M.map φ.toMonoidHom) U).mp hxy
    obtain ⟨s, hs, hst⟩ := t.property
    change φ s = (t : T) at hst
    refine ⟨⟨s, hs⟩, ?_⟩
    change φ s * x = φ s * y
    rw [hst]
    exact ht

/-- 概要：元の評価加群の標準係数拡大は、局所化先の評価加群。
方針：元の係数射の加群局所化性を通常テンソル普遍性へ移す。
規約：二つの評価射と標準係数射を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二因子源の左因子の実比較。 -/
def unconditionalEvaluationLocalizationEquiv
    (M : Submonoid R) [IsLocalization M S] [IsLocalization (M.map φ.toMonoidHom) U] :
    (ModuleCat.extendScalars (algebraMap R S)).obj (baseChangeScalarModule φ) ≃ₗ[S]
      baseChangeScalarModule ψ := by
  let N := (ModuleCat.restrictScalars (algebraMap R S)).obj (baseChangeScalarModule ψ)
  letI : Module S N := Module.compHom U ψ
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let f := unconditionalEvaluationCoefficientMap φ ψ hcomm
  have : IsLocalizedModule M f :=
    unconditionalEvaluationCoefficientMap_isLocalizedModule φ ψ hcomm M
  let h := IsLocalizedModule.isBaseChange M S f
  exact (extendScalarsObjEquivTensor R S (baseChangeScalarModule φ)).trans h.equiv

end SerrePositivity.BhattScholze.Andre

end LocalizedEvaluationModule

/-! ## 単元分母での実源 δ 射の可逆性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の実源を、分母が単元となる係数環上で調べる。

## 方針
自由 δ 射の一意性から分母の乗法性を示し、逆単元で逆射を構成する。

## 規約
元の自由 δ 環とその実源射を用い、係数環の p 正則性を仮定しない。

## 使われ方
raw 包の p 正則性を調べる際の、Frobenius 安定局所化側の比較を供給する。
-/

@[expose] public noncomputable section SourceUnitDenominator

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 概要：分母を掛ける実源 δ 射の合成は、積を掛ける実源射。
方針：係数と初期変数上で計算し、自由 δ 射の一意性を使う。
規約：分母の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化側の逆射。 -/
theorem unconditionalDeltaDivisionSourceMap_comp (D : DeltaStructure p A) (d e : A) :
    (deltaDivisionSourceMap (σ := σ) D d).comp (deltaDivisionSourceMap D e) =
      deltaDivisionSourceMap D (e * d) := by
  let F := relativeFreeDeltaStructure σ D
  let g := (deltaDivisionSourceMap (σ := σ) D d).comp (deltaDivisionSourceMap D e)
  have hg : F.IsDeltaHom F g := by
    intro x
    change deltaDivisionSourceMap D d (deltaDivisionSourceMap D e (F.delta x)) = _
    rw [deltaDivisionSourceMap_isDeltaHom D e, deltaDivisionSourceMap_isDeltaHom D d]
    rfl
  have hC : g.comp MvPolynomial.C = MvPolynomial.C := by
    ext r
    simp [g, RingHom.comp_apply, deltaDivisionSourceMap_C]
  have hX (s : σ) : g (MvPolynomial.X (s, 0)) =
      MvPolynomial.C (e * d) * MvPolynomial.X (s, 0) := by
    simp [g, RingHom.comp_apply, deltaDivisionSourceMap_X, deltaDivisionSourceMap_C,
      map_mul, mul_assoc]
  exact (existsUnique_relativeFreeDeltaHom D F MvPolynomial.C
    (relativeFreeDeltaStructure_C_isDeltaHom σ D)
    (fun s => MvPolynomial.C (e * d) * MvPolynomial.X (s, 0))).unique
      ⟨hg, hC, hX⟩ ⟨deltaDivisionSourceMap_isDeltaHom D _,
        by apply RingHom.ext; intro r; exact deltaDivisionSourceMap_C D _ r,
        by intro s; exact deltaDivisionSourceMap_X D _ s 0⟩

/-- 概要：単元を分母とする実源射の環同型。
方針：逆単元の実源射との合成を計算する。
規約：元の自由 δ 環そのものの自己同型。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母可逆な部分。 -/
def unconditionalDeltaDivisionSourceUnitEquiv (D : DeltaStructure p A) (d : Aˣ) :
    RelativeFreeDeltaRing (R := A) σ ≃+* RelativeFreeDeltaRing (R := A) σ :=
  { deltaDivisionSourceMap D (d : A) with
    invFun := deltaDivisionSourceMap D ((d⁻¹ : Aˣ) : A)
    left_inv := by
      intro x
      have h := unconditionalDeltaDivisionSourceMap_comp (σ := σ) D
        ((d⁻¹ : Aˣ) : A) (d : A)
      rw [Units.mul_inv, deltaDivisionSourceMap_one] at h
      exact DFunLike.congr_fun h x
    right_inv := by
      intro x
      have h := unconditionalDeltaDivisionSourceMap_comp (σ := σ) D
        (d : A) ((d⁻¹ : Aˣ) : A)
      rw [Units.inv_mul, deltaDivisionSourceMap_one] at h
      exact DFunLike.congr_fun h x }

/-- 概要：分母が単元なら元の実源射は全単射。
方針：逆単元から構成した環同型の全単射性を使う。
規約：同型に置き換えず、元の環射について述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化後の実源。 -/
theorem unconditionalDeltaDivisionSourceMap_bijective_of_isUnit
    (D : DeltaStructure p A) (d : A) (hd : IsUnit d) :
    Function.Bijective (deltaDivisionSourceMap (σ := σ) D d) := by
  obtain ⟨u, rfl⟩ := hd
  exact (unconditionalDeltaDivisionSourceUnitEquiv (σ := σ) D u).bijective

/-- 概要：係数 δ 射の多項式への拡大も、実自由 δ 構造を保つ。
方針：自由 δ 評価射と、全 δ 座標上で一致することを示す。
規約：係数射の単射性・平坦性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数局所化との両立。 -/
theorem unconditionalRelativeFreeMap_isDeltaHom
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (E : DeltaStructure p B)
    (q : A →+* B) (hq : D.IsDeltaHom E q) :
    (relativeFreeDeltaStructure σ D).IsDeltaHom (relativeFreeDeltaStructure σ E)
      (MvPolynomial.map q) := by
  let g := relativeFreeDeltaEval (relativeFreeDeltaStructure σ E) (MvPolynomial.C.comp q)
    (fun s : σ => MvPolynomial.X (s, 0))
  have hg : (relativeFreeDeltaStructure σ D).IsDeltaHom
      (relativeFreeDeltaStructure σ E) g := by
    apply relativeFreeDeltaEval_isDeltaHom
    intro x
    change MvPolynomial.C (q (D.delta x)) = _
    rw [hq x, ← relativeFreeDeltaStructure_delta_C]
    rfl
  have he : g = MvPolynomial.map q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [g, RingHom.comp_apply]
    · rintro ⟨s, n⟩
      rw [show g (MvPolynomial.X (s, n)) =
          (relativeFreeDeltaStructure σ E).delta^[n] (MvPolynomial.X (s, 0)) from
            relativeFreeDeltaEval_X _ _ _ _ _, MvPolynomial.map_X]
      exact (relativeFreeDeltaHom_X_iterates E (relativeFreeDeltaStructure σ E)
        (RingHom.id _) (fun _ => rfl) s n).symm
  rw [he] at hg
  exact hg

/-- 概要：実源の分母倍射は係数 δ 射と可換。
方針：係数と初期生成元を比較し、δ 射の一意性で全座標へ延長する。
規約：元の多項式係数射を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実源の局所化比較。 -/
theorem unconditionalDeltaDivisionSourceMap_natural
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (E : DeltaStructure p B)
    (q : A →+* B) (hq : D.IsDeltaHom E q) (d : A) :
    (MvPolynomial.map q).comp (deltaDivisionSourceMap (σ := σ) D d) =
      (deltaDivisionSourceMap E (q d)).comp (MvPolynomial.map q) := by
  let F := relativeFreeDeltaStructure σ D
  let G := relativeFreeDeltaStructure σ E
  let l := (MvPolynomial.map q).comp (deltaDivisionSourceMap (σ := σ) D d)
  let r := (deltaDivisionSourceMap (σ := σ) E (q d)).comp (MvPolynomial.map q)
  have hl : F.IsDeltaHom G l := by
    intro x
    change MvPolynomial.map q (deltaDivisionSourceMap D d (F.delta x)) = _
    rw [deltaDivisionSourceMap_isDeltaHom D d,
      unconditionalRelativeFreeMap_isDeltaHom D E q hq]
    rfl
  have hr : F.IsDeltaHom G r := by
    intro x
    change deltaDivisionSourceMap E (q d) (MvPolynomial.map q (F.delta x)) = _
    rw [unconditionalRelativeFreeMap_isDeltaHom D E q hq,
      deltaDivisionSourceMap_isDeltaHom E (q d)]
    rfl
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply, deltaDivisionSourceMap_C]
  · rintro ⟨s, n⟩
    change l (MvPolynomial.X (s, n)) = r (MvPolynomial.X (s, n))
    rw [relativeFreeDeltaHom_X_iterates D G l hl s n,
      relativeFreeDeltaHom_X_iterates D G r hr s n]
    congr 1
    simp [l, r, RingHom.comp_apply, deltaDivisionSourceMap_X]

/-- 概要：Frobenius 安定化した分母局所化では、実源射は全単射。
方針：局所化の δ 構造と分母の単元性を使う。
規約：任意の実局所化環に適用でき、p 正則性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母可逆部分の比較。 -/
theorem unconditionalDeltaDivisionSourceMap_bijective_localization
    (D : DeltaStructure p A) (d : A) (B : Type w) [CommRing B] [Algebra A B]
    [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B] :
    Function.Bijective (deltaDivisionSourceMap (σ := σ)
      (D.localization (D.frobeniusDenominators (Submonoid.powers d)) B
        (D.frobeniusDenominators_stable (Submonoid.powers d))) (algebraMap A B d)) := by
  apply unconditionalDeltaDivisionSourceMap_bijective_of_isUnit
  exact IsLocalization.map_units B
    ⟨d, D.le_frobeniusDenominators (Submonoid.powers d) (Submonoid.mem_powers d)⟩

/-- 概要：mod p 係数射上で d が単元なら、安定化した全分母も単元。
方針：Frobenius の像が p 冪になることを反復し、乗法的閉包へ延長する。
規約：終域の δ 構造は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の安定局所化と通常の mod p 局所化の比較。 -/
theorem unconditionalFrobeniusDenominators_isUnit_mod_prime
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A)
    (q : A →+* B) (hp : q (p : A) = 0) (hd : IsUnit (q d))
    (s : D.frobeniusDenominators (Submonoid.powers d)) : IsUnit (q s) := by
  have hφ (x : A) : q (D.frobeniusLift x) = (q x) ^ p := by
    rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, hp, zero_mul, add_zero]
  have hiter (r : Submonoid.powers d) (n : ℕ) :
      IsUnit (q ((D.frobeniusLift : A → A)^[n] r)) := by
    induction n with
    | zero =>
      obtain ⟨m, hm⟩ := r.property
      change IsUnit (q (r : A))
      rw [← hm, map_pow]
      exact hd.pow m
    | succ n ih =>
      rw [Function.iterate_succ_apply', hφ]
      exact ih.pow p
  exact Submonoid.closure_induction
    (fun x hx => by obtain ⟨⟨r, n⟩, rfl⟩ := hx; exact hiter r n)
    (by simp)
    (fun x y _ _ hx hy => by rw [map_mul]; exact hx.mul hy) s.property

/-- 概要：安定化した分母集合の mod p 像は、元の分母像の冪集合そのもの。
方針：Frobenius 反復像が p 冪へ移ることと、元の分母集合の包含を使う。
規約：任意の p を零に送る環射について述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの実局所化の同定。 -/
theorem unconditionalFrobeniusDenominators_map_mod_prime
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A)
    (q : A →+* B) (hp : q (p : A) = 0) :
    (D.frobeniusDenominators (Submonoid.powers d)).map q.toMonoidHom =
      Submonoid.powers (q d) := by
  have hφ (x : A) : q (D.frobeniusLift x) = (q x) ^ p := by
    rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, hp, zero_mul, add_zero]
  have hiter (r : Submonoid.powers d) (n : ℕ) :
      q ((D.frobeniusLift : A → A)^[n] r) ∈ Submonoid.powers (q d) := by
    induction n with
    | zero =>
      obtain ⟨m, hm⟩ := r.property
      change q (r : A) ∈ Submonoid.powers (q d)
      rw [← hm, map_pow]
      exact pow_mem (Submonoid.mem_powers _) m
    | succ n ih =>
      rw [Function.iterate_succ_apply', hφ]
      exact pow_mem ih p
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact Submonoid.closure_induction
      (fun x hx => by obtain ⟨⟨r, n⟩, rfl⟩ := hx; exact hiter r n)
      (by simp)
      (fun x y _ _ hx hy => by rw [map_mul]; exact mul_mem hx hy) hs
  · rw [← Submonoid.map_powers q d]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, D.le_frobeniusDenominators (Submonoid.powers d) hx, rfl⟩

/-- 概要：実安定局所化の mod p 商は、元の mod p 商の d 局所化。
方針：局所化とイデアル商の可換性に、分母集合の像の等式を適用する。
規約：終域は元の局所化環 B の実イデアル商。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの局所化を同じ対象上で比較する。 -/
theorem unconditionalSaturatedLocalization_mod_prime_isLocalizationAway
    (D : DeltaStructure p A) (d : A) (B : Type w) [CommRing B] [Algebra A B]
    [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B] :
    IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {(p : A)}) d)
      (B ⧸ (Ideal.span {(p : A)}).map (algebraMap A B)) := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hp : q (p : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  change IsLocalization (Submonoid.powers (q d)) _
  rw [← unconditionalFrobeniusDenominators_map_mod_prime D d q hp]
  exact IsLocalization.of_surjective (D.frobeniusDenominators (Submonoid.powers d)) B
    q Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk ((Ideal.span {(p : A)}).map (algebraMap A B)))
    Ideal.Quotient.mk_surjective rfl (by simp [q])

end SerrePositivity.BhattScholze.Andre

end SourceUnitDenominator

/-! ## 実自由 δ 源の右因子と係数局所化の比較

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の実源作用を、Frobenius 安定係数局所化へ運ぶ。

## 方針
実係数射との可換性と、分母係数を固定することを一般加群局所化へ供給する。

## 規約
元の実源射と標準多項式係数射を用いる。

## 使われ方
元の二因子導来源の局所化比較の右因子を供給する。
-/

@[expose] public noncomputable section LocalizedDeltaSourceTarget

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A)
variable (B : Type u) [CommRing B] [Algebra A B]
variable [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B]
local notation "T" => D.frobeniusDenominators (Submonoid.powers d)
local notation "E" => D.localization T B (D.frobeniusDenominators_stable (Submonoid.powers d))
local notation "LA" => RelativeFreeDeltaRing (R := A) σ
local notation "LB" => RelativeFreeDeltaRing (R := B) σ
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- 概要：元の実源の右因子の標準係数拡大は、局所化 δ 源の右因子。
方針：元の実射の可換性と係数上の恒等性を、加群局所化の具体的比較へ渡す。
規約：元の二つのスカラー作用を保持する線形同型。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実導来源の局所化比較。 -/
def unconditionalDeltaSourceTargetLocalizationEquiv :
    (ModuleCat.extendScalars (MvPolynomial.map (algebraMap A B))).obj
        (baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)) ≃ₗ[LB]
      baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) E (algebraMap A B d)) := by
  let α := deltaDivisionSourceMap (σ := σ) D d
  let β := deltaDivisionSourceMap (σ := σ) E (algebraMap A B d)
  have hcomm : β.comp (algebraMap LA LB) = (algebraMap LA LB).comp α := by
    exact (unconditionalDeltaDivisionSourceMap_natural D E (algebraMap A B)
      (D.isDeltaHom_localization T B
        (D.frobeniusDenominators_stable (Submonoid.powers d))) d).symm
  have hfix (s : (T).map (MvPolynomial.C : A →+* LA)) : α s = s := by
    obtain ⟨r, hr, hs⟩ := s.property
    rw [← hs]
    exact deltaDivisionSourceMap_C D d r
  exact unconditionalScalarModuleLocalizationEquiv α β hcomm
    ((T).map (MvPolynomial.C : A →+* LA)) hfix

end SerrePositivity.BhattScholze.Andre

end LocalizedDeltaSourceTarget

/-! ## 実自由 δ 源の左評価因子と係数局所化の比較

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の実評価作用を、Frobenius 安定係数局所化へ運ぶ。

## 方針
評価射の係数射との可換性と、分母係数の像を一般加群局所化へ供給する。

## 規約
元の分子の像と標準係数拡大を保持する。

## 使われ方
元の二因子導来源の局所化比較の左因子を供給する。
-/

@[expose] public noncomputable section LocalizedDeltaSourceEvaluation

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

/-- 概要：実源評価は、分子を同じ係数 δ 射で移す操作と可換。
方針：係数と全 δ 座標で計算し、δ 保存性を反復する。
規約：係数射の単射性・平坦性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化後の左因子の作用。 -/
theorem unconditionalDeltaSourceEvaluation_natural
    {B : Type u} [CommRing B] (D : DeltaStructure p A) (E : DeltaStructure p B)
    (q : A →+* B) (hq : D.IsDeltaHom E q) (a : σ → A) :
    (deltaDivisionSourceEval E (fun s => q (a s))).comp (MvPolynomial.map q) =
      q.comp (deltaDivisionSourceEval D a) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [RingHom.comp_apply, deltaDivisionSourceEval_C]
  · rintro ⟨s, n⟩
    simp only [RingHom.comp_apply, MvPolynomial.map_X, deltaDivisionSourceEval_X]
    exact ((show Function.Semiconj q D.delta E.delta from hq).iterate_right n (a s)).symm

variable (D : DeltaStructure p A) (d : A) (a : σ → A)
variable (B : Type u) [CommRing B] [Algebra A B]
variable [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B]
local notation "T" => D.frobeniusDenominators (Submonoid.powers d)
local notation "E" => D.localization T B (D.frobeniusDenominators_stable (Submonoid.powers d))
local notation "LA" => RelativeFreeDeltaRing (R := A) σ
local notation "LB" => RelativeFreeDeltaRing (R := B) σ
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- 概要：元の実源の左評価因子の標準係数拡大は、局所化 δ 源の評価因子。
方針：元の評価射の可換性と分母像の同定を、加群局所化比較へ渡す。
規約：元の分子族の像と標準多項式係数射を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実二因子導来源の局所化比較。 -/
def unconditionalDeltaSourceEvaluationLocalizationEquiv :
    (ModuleCat.extendScalars (MvPolynomial.map (algebraMap A B))).obj
        (baseChangeScalarModule (deltaDivisionSourceEval D a)) ≃ₗ[LB]
      baseChangeScalarModule (deltaDivisionSourceEval E (fun s => algebraMap A B (a s))) := by
  let φ := deltaDivisionSourceEval D a
  let ψ := deltaDivisionSourceEval E (fun s => algebraMap A B (a s))
  have hcomm : ψ.comp (algebraMap LA LB) = (algebraMap A B).comp φ :=
    unconditionalDeltaSourceEvaluation_natural D E (algebraMap A B)
      (D.isDeltaHom_localization T B
        (D.frobeniusDenominators_stable (Submonoid.powers d))) a
  let M := (T).map (MvPolynomial.C : A →+* LA)
  have hmap : M.map φ.toMonoidHom = T := by
    ext x
    constructor
    · rintro ⟨z, hz, hzx⟩
      obtain ⟨r, hr, rfl⟩ := hz
      change φ (MvPolynomial.C r) = x at hzx
      rw [deltaDivisionSourceEval_C] at hzx
      exact hzx ▸ hr
    · intro hx
      exact ⟨MvPolynomial.C x, ⟨x, hx, rfl⟩, deltaDivisionSourceEval_C D a x⟩
  have : IsLocalization (M.map φ.toMonoidHom) B := hmap.symm ▸ inferInstance
  exact unconditionalEvaluationLocalizationEquiv φ ψ hcomm M

end SerrePositivity.BhattScholze.Andre

end LocalizedDeltaSourceEvaluation

/-! ## 単元分母での元の二因子導来源の純性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の実源の分母可逆部分では、高次 Tor は消える。

## 方針
実源射の逆射を使って右因子を自由な一階加群へ比較する。
Tor の対称性と元の標準 augmentation に沿って純性を得る。

## 規約
元の係数作用を保つ。分子の正則性・モニック性・係数環の p 正則性は不要。

## 使われ方
元の源の局所化比較後に、局所化側の負次数消滅を供給する。
-/

@[expose] public noncomputable section SourceUnitPurity

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
local notation "L" => RelativeFreeDeltaRing (R := A) σ

/-- 概要：単元分母の実源射による係数加群は平坦。
方針：逆射を使い、同じ係数環の自由一階加群へ線形同型を作る。
規約：元の実源射によるスカラー作用を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化側の Tor 消滅。 -/
theorem unconditionalSourceUnit_scalarModule_flat
    (D : DeltaStructure p A) (d : A) (hd : IsUnit d) :
    Module.Flat L (baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)) := by
  let α := deltaDivisionSourceMap (σ := σ) D d
  let e := RingEquiv.ofBijective α
    (unconditionalDeltaDivisionSourceMap_bijective_of_isUnit D d hd)
  let eM : baseChangeScalarModule α ≃ₗ[L] L :=
    { e.symm.toAddEquiv with
      map_smul' := by
        intro r x
        change L at x
        change e.symm (α r * x) = r * e.symm x
        rw [map_mul]
        congr 1
        exact e.symm_apply_apply r }
  exact Module.Flat.of_linearEquiv eM

/-- 概要：単元分母の実二因子源の高次 Tor は零。
方針：右因子の平坦性と Tor の対称性を使う。
規約：分子族は任意でよい。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準 augmentation の同型性。 -/
theorem unconditionalSourceUnit_tor_isZero
    (D : DeltaStructure p A) (d : A) (hd : IsUnit d) (a : σ → A)
    (n : ℕ) (hn : 0 < n) :
    IsZero (((Tor (ModuleCat L) n).obj
      (baseChangeScalarModule (deltaDivisionSourceEval D a))).obj
        (baseChangeScalarModule (deltaDivisionSourceMap D d))) := by
  let Mβ := baseChangeScalarModule (deltaDivisionSourceEval D a)
  let Mα := baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
  have : Module.Flat L Mα := unconditionalSourceUnit_scalarModule_flat D d hd
  cases n with
  | zero => omega
  | succ n =>
    have : Subsingleton (TorModule L (n + 1) Mα Mβ) :=
      torModule_subsingleton_of_flat Mα Mβ n
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torComm (n + 1) Mβ Mα).injective.subsingleton

/-- 概要：単元分母では元の二因子導来源の標準 augmentation が同型。
方針：同じ実二因子の Tor 消滅を標準 augmentation の判定へ渡す。
規約：通常テンソルへの元の射について述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化側の純性比較。 -/
theorem unconditionalSourceUnit_augmentation_isIso
    (D : DeltaStructure p A) (d : A) (hd : IsUnit d) (a : σ → A) :
    IsIso ((boundedAboveDerivedTensorModuleAugmentation
      (baseChangeScalarModule (deltaDivisionSourceEval D a))).app
        (baseChangeScalarModule (deltaDivisionSourceMap D d))) :=
  derivedTensorAugmentation_isIso_of_tor _ _
    (unconditionalSourceUnit_tor_isZero D d hd a)

/-- 概要：単元分母での元の二因子導来源は全非零次数でホモロジーが消える。
方針：元の標準 augmentation の同型で通常テンソルの single へ移す。
規約：完備化・ねじれ除去は行わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化側の消滅判定。 -/
theorem unconditionalSourceUnit_homology_isZero
    (D : DeltaStructure p A) (d : A) (hd : IsUnit d) (a : σ → A)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L) i).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj
            (baseChangeScalarModule (deltaDivisionSourceEval D a)),
          boundedAboveDerivedSingleFunctor.obj
            (baseChangeScalarModule (deltaDivisionSourceMap D d)))).obj) := by
  let Mβ := baseChangeScalarModule (deltaDivisionSourceEval D a)
  let Mα := baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
  have := unconditionalSourceUnit_augmentation_isIso D d hd a
  exact (derivedSingleHomology_isZero ((CategoryTheory.MonoidalCategory.tensorLeft Mβ).obj Mα)
    i hi).of_iso ((DerivedCategory.homologyFunctor (ModuleCat L) i).mapIso
      (asIso ((boundedAboveDerivedTensorModuleAugmentation Mβ).app Mα)))

/-- 概要：安定局所化した係数と元の分子像による実源の非零次ホモロジーは零。
方針：元の分母の単元性を局所化から供給して前の純性定理を使う。
規約：係数と分子の像は標準局所化射で指定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の源の係数局所化後の比較先。 -/
theorem unconditionalSourceSaturatedLocalization_homology_isZero
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (B : Type u) [CommRing B] [Algebra A B]
    [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B]
    (i : ℤ) (hi : i ≠ 0) :
    let E := D.localization (D.frobeniusDenominators (Submonoid.powers d)) B
      (D.frobeniusDenominators_stable (Submonoid.powers d))
    let α := deltaDivisionSourceMap (σ := σ) E (algebraMap A B d)
    let β := deltaDivisionSourceEval E (fun s => algebraMap A B (a s))
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (RelativeFreeDeltaRing (R := B) σ)) i).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule β),
          boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule α))).obj) := by
  apply unconditionalSourceUnit_homology_isZero _ _ _ _ i hi
  exact IsLocalization.map_units B
    ⟨d, D.le_frobeniusDenominators (Submonoid.powers d) (Submonoid.mem_powers d)⟩

end SerrePositivity.BhattScholze.Andre

end SourceUnitPurity

/-! ## 元の実二因子 δ 源の係数局所化

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の実導来源を、係数局所化上の実源へ比較する。

## 方針
平坦係数拡大と実導来テンソルの比較に、左右因子の元の係数拡大同型を合成する。

## 規約
分子像・係数射・二つの実源作用を保持する。完備化やねじれ除去を行わない。

## 使われ方
元の実源の局所化側のホモロジー消滅を供給する。
-/

@[expose] public noncomputable section LocalizedDeltaSourceTensor

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
variable (B : Type u) [CommRing B] [Algebra A B]
variable [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B]
local notation "T" => D.frobeniusDenominators (Submonoid.powers d)
local notation "E" => D.localization T B (D.frobeniusDenominators_stable (Submonoid.powers d))
local notation "LA" => RelativeFreeDeltaRing (R := A) σ
local notation "LB" => RelativeFreeDeltaRing (R := B) σ
local notation "qL" => MvPolynomial.map (σ := σ × ℕ) (algebraMap A B)
local notation "Mβ" => baseChangeScalarModule (deltaDivisionSourceEval D a)
local notation "Mα" => baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
local notation "Nβ" => baseChangeScalarModule
  (deltaDivisionSourceEval E (fun s => algebraMap A B (a s)))
local notation "Nα" => baseChangeScalarModule
  (deltaDivisionSourceMap (σ := σ) E (algebraMap A B d))
local notation "XA" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "XB" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Nβ, boundedAboveDerivedSingleFunctor.obj Nα)
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- 概要：元の実二因子導来源の標準係数拡大は、局所化上の実二因子源。
方針：平坦な多項式係数局所化と、元の左右因子の標準比較を合成する。
規約：二因子の順序・分子像・標準係数射を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化側の消滅の移送。 -/
def unconditionalDeltaSourceTensorLocalizationIso :
    (boundedAboveDerivedBaseChange qL).obj XA ≅ XB := by
  letI : Module.Flat LA LB :=
    IsLocalization.flat LB ((T).map (MvPolynomial.C : A →+* LA))
  let eβ := (unconditionalDeltaSourceEvaluationLocalizationEquiv D d a B).toModuleIso
  let eα := (unconditionalDeltaSourceTargetLocalizationEquiv (σ := σ) D d B).toModuleIso
  exact boundedAboveDerivedTensorBaseChangeModuleIso qL Mβ Mα
      (scalarExtensionTorVanishing_of_flat_algebra Mβ)
      (scalarExtensionTorVanishing_of_flat_algebra Mα) ≪≫
    boundedAboveDerivedTensor.mapIso
      (Iso.prod (boundedAboveDerivedSingleFunctor.mapIso eβ)
        (boundedAboveDerivedSingleFunctor.mapIso eα))

/-- 概要：元の実導来源の標準局所化後は、全非零次数のホモロジーが消える。
方針：元の導来局所化同型で、単元分母の実源の消滅へ移す。
規約：元の対象を係数拡大したものについて述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 源の局所化と完備化による純性検出。 -/
theorem unconditionalDeltaSourceTensor_localization_homology_isZero
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat LB) i).obj
      ((boundedAboveDerivedBaseChange qL).obj XA).obj) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat LB) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (unconditionalDeltaSourceTensorLocalizationIso D d a B))
  exact (unconditionalSourceSaturatedLocalization_homology_isZero D d a B i hi).of_iso e

end SerrePositivity.BhattScholze.Andre

end LocalizedDeltaSourceTensor

/-! ## 単元分母の実源と元の評価加群

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の分母可逆部分の実源を、元の評価加群へ比較する。

## 方針
右因子の実源自己同型を逆にして自由一階加群へ移し、標準 augmentation を合成する。

## 規約
元の評価による作用を保持し、通常の single との具体的な同型を作る。

## 使われ方
局所化先の p 正則性から、元の実源の局所化後の p 錐純性を供給する。
-/

@[expose] public noncomputable section SourceUnitSingle

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- 概要：右因子が自由一階で標準 augmentation が同型なら、実テンソルは左因子の single。
方針：右因子の同型とテンソルの右単位同型を合成する。
規約：標準 augmentation の同型性を明示する一般補題。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的な元の作用の比較。 -/
def unconditionalTensorSingleIso_of_unit_right
    {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) (eN : N ≅ ModuleCat.of R R)
    (h : IsIso ((boundedAboveDerivedTensorModuleAugmentation M).app N)) :
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)).obj ≅
        (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M := by
  have := h
  let e := (tensorLeft M).mapIso eN ≪≫ (ρ_ M)
  exact asIso ((boundedAboveDerivedTensorModuleAugmentation M).app N) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat R) 0).mapIso e

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (hd : IsUnit d) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "Mα" => baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
local notation "Mβ" => baseChangeScalarModule (deltaDivisionSourceEval D a)
local notation "X" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)

/-- 概要：単元分母で作用する右因子は、元の係数環の自由一階加群と線形同型。
方針：実源自己同型の逆を台写像にする。
規約：元の自己射作用を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実源の H⁰ の同定。 -/
def unconditionalSourceUnitScalarModuleEquiv : Mα ≃ₗ[L] L := by
  let e := RingEquiv.ofBijective (deltaDivisionSourceMap (σ := σ) D d)
    (unconditionalDeltaDivisionSourceMap_bijective_of_isUnit D d hd)
  exact
    { e.symm.toAddEquiv with
      map_smul' := by
        intro r x
        change L at x
        change e.symm (deltaDivisionSourceMap D d r * x) = r * e.symm x
        rw [map_mul]
        congr 1
        exact e.symm_apply_apply r }

set_option backward.isDefEq.respectTransparency true in
/-- 概要：単元分母の元の実二因子源は、元の評価加群の single と同型。
方針：標準 augmentation と右因子の自由一階比較を合成する。
規約：元の β による係数作用を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化先の p 錐の計算。 -/
def unconditionalSourceUnitSingleIso :
    (X).obj ≅ (DerivedCategory.singleFunctor (ModuleCat L) 0).obj Mβ := by
  let eM : Mα ≅ ModuleCat.of L L := (unconditionalSourceUnitScalarModuleEquiv D d hd).toModuleIso
  with_reducible exact (unconditionalTensorSingleIso_of_unit_right Mβ Mα eM
    (unconditionalSourceUnit_augmentation_isIso D d hd a))

include hd in
/-- 概要：係数環の p が正則なら、単元分母の元の実源の p 錐は非零次数で消える。
方針：元の評価加群の p 正則性と、実スカラー錐の通常商比較を使う。
規約：分子の正則性・モニック性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化側の先行 p 還元。 -/
theorem unconditionalSourceUnit_primeCone_homology_isZero
    (hp : IsSMulRegular A (p : A)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L) i).obj
      ((derivedScalarConeFunctor L (p : L)).obj (X).obj)) := by
  have hM : IsSMulRegular Mβ (p : L) := by
    intro x y hxy
    change A at x y
    change deltaDivisionSourceEval D a (p : L) * x =
      deltaDivisionSourceEval D a (p : L) * y at hxy
    rw [map_natCast] at hxy
    exact hp hxy
  let e := (derivedScalarConeFunctor L (p : L)).mapIso
    (unconditionalSourceUnitSingleIso D d hd a)
  have eQ := derivedScalarConeModuleQuotientIso (p : L) Mβ hM 1
  rw [pow_one] at eQ
  exact (derivedSingleHomology_isZero (modulePowerReduction (p : L) Mβ 1) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L) i).mapIso (e ≪≫ eQ))

end SerrePositivity.BhattScholze.Andre

end SourceUnitSingle

/-! ## 元の実源の p 錐の局所化後の純性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の実 p 錐は、安定係数局所化後に次数零に集中する。

## 方針
元の実局所化とスカラー錐の比較を、単元分母の元の評価加群の p 正則性へ接続する。

## 規約
必要な p 正則性は係数環上だけであり、prism 商の p 正則性は要求しない。

## 使われ方
元の raw 源の p 錐の負次数を、d 冪ねじれとして検出する。
-/

@[expose] public noncomputable section LocalizedDeltaSourcePrimeCone

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
variable (B : Type u) [CommRing B] [Algebra A B]
variable [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B]
local notation "T" => D.frobeniusDenominators (Submonoid.powers d)
local notation "E" => D.localization T B (D.frobeniusDenominators_stable (Submonoid.powers d))
local notation "LA" => RelativeFreeDeltaRing (R := A) σ
local notation "LB" => RelativeFreeDeltaRing (R := B) σ
local notation "qL" => MvPolynomial.map (σ := σ × ℕ) (algebraMap A B)
local notation "Mβ" => baseChangeScalarModule (deltaDivisionSourceEval D a)
local notation "Mα" => baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
local notation "XA" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- 概要：元の実源の先行 p 錐の局所化後は、全非零次ホモロジーが消える。
方針：元の二因子源の局所化比較と、局所化先の評価加群上の p 正則性を使う。
規約：係数環 A の p 正則性だけを仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の raw 源の p 正則性検出。 -/
theorem unconditionalDeltaSourcePrimeCone_localization_homology_isZero
    (hp : IsSMulRegular A (p : A)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat LB) i).obj
      ((boundedAboveDerivedBaseChange qL).obj
        ((boundedAboveDerivedScalarCone LA (p : LA)).obj XA)).obj) := by
  letI : Module.Flat A B := IsLocalization.flat B T
  have hpB : IsSMulRegular B (p : B) := by
    simpa only [map_natCast] using hp.of_flat (S := B)
  have hdB : IsUnit (algebraMap A B d) := IsLocalization.map_units B
    ⟨d, D.le_frobeniusDenominators (Submonoid.powers d) (Submonoid.mem_powers d)⟩
  let e₁ := boundedAboveDerivedBaseChangeScalarConeIso qL (p : LA) XA
  have e₂ := (derivedScalarConeFunctor LB (p : LB)).mapIso
    (DerivedCategory.Minus.ι.mapIso (unconditionalDeltaSourceTensorLocalizationIso D d a B))
  rw [map_natCast] at e₁
  exact (unconditionalSourceUnit_primeCone_homology_isZero E (algebraMap A B d) hdB
    (fun s => algebraMap A B (a s)) hpB i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat LB) i).mapIso (e₁ ≪≫ e₂))

end SerrePositivity.BhattScholze.Andre

end LocalizedDeltaSourcePrimeCone

/-! ## 完備化と冪ねじれによる負次数消滅の検出

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の raw 源を、完備化と局所化から比較するための判定。

## 方針
完備化単位の Koszul 同値性により、負次数ホモロジーの分母作用は単射になる。
各元の分母冪ねじれと合わせて消滅させる。

## 規約
元の導来対象を用いる。環の正則性・有界ねじれ・対象の完備性は仮定しない。

## 使われ方
raw 源の局所化側で得られる冪ねじれ性と、既証明の完備化純性を接続する。
-/

@[expose] public noncomputable section CompletionTorsionDetection

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)

/-- 概要：隣接する二次数の消滅は、実スカラー錐の中間ホモロジーを消す。
方針：実写像錐の長完全列を任意の複体モデルで使う。
規約：対象の完備性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化側の消滅。 -/
theorem unconditionalScalarCone_homology_isZero
    (X : ConcreteDerivedCategory R) (i : ℤ)
    (hi : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X))
    (hi1 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (i + 1)).obj X)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let eX := DerivedCategory.Q.objObjPreimageIso X
  have hK (n : ℤ) (hn : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj X)) :
      IsZero (K.homology n) :=
    hn.of_iso (((DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat R) n).mapIso eX)
  have hc : IsZero (((scalarConeFunctor a).obj K).homology i) :=
    (Cone.exact₃ (smulId a K) i (i + 1) rfl).isZero_X₂
      ((hK i hi).eq_zero_of_src _) ((hK (i + 1) hi1).eq_zero_of_tgt _)
  let ec := ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app
      ((scalarConeFunctor a).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      ((derivedScalarConeComparison R a).symm.app K ≪≫
        (derivedScalarConeFunctor R a).mapIso eX)
  exact hc.of_iso ec.symm

/-- 概要：完備化に負次数ホモロジーがなければ、元の負次数の分母作用は単射。
方針：完備化単位のスカラー錐上の同型と長完全列を使う。
規約：元の対象が完備である必要はない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化側の冪ねじれとの接続。 -/
theorem unconditionalNegativeHomology_smul_injective_of_completion_isGE
    (X : ConcreteDerivedCategory R)
    (hX : ((derivedComplexCompletionFunctor R a).obj X).IsGE 0)
    (i : ℤ) (hi : i < 0) :
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X => a • x) := by
  let Y := (derivedComplexCompletionFunctor R a).obj X
  have hz (n : ℤ) (hn : n < 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj Y) :=
    (DerivedCategory.isGE_iff Y 0).mp hX n hn
  have hcone := unconditionalScalarCone_homology_isZero a Y (i - 1)
    (hz (i - 1) (by omega)) (hz (i - 1 + 1) (by omega))
  let η := (derivedComplexCompletionUnit R a).app X
  have hη := derivedScalarCone_map_isIso_of_completion R a η
    (derivedComplexCompletionFunctor_map_unit_isIso R a X) 1
  rw [pow_one] at hη
  have := hη
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) (i - 1)).mapIso
    (asIso ((derivedScalarConeFunctor R a).map η))
  exact derived_homology_smul_injective_of_scalarCone_isZero a X i (hcone.of_iso e)

/-- 概要：完備化の負次数消滅と元の負次数の各元冪ねじれ性は、元の負次数を消す。
方針：前の単射性を反復し、冪で零になる各元を零へ戻す。
規約：ねじれ指数は元ごとに異なってよい。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 源の純性判定。 -/
theorem unconditional_isGE_of_completion_isGE_of_negative_power_torsion
    (X : ConcreteDerivedCategory R)
    (hX : ((derivedComplexCompletionFunctor R a).obj X).IsGE 0)
    (ht : ∀ i : ℤ, i < 0 →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X,
        ∃ n : ℕ, a ^ n • x = 0) : X.IsGE 0 := by
  apply (DerivedCategory.isGE_iff X 0).mpr
  intro i hi
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨n, hn⟩ := ht i hi x
  have ha := unconditionalNegativeHomology_smul_injective_of_completion_isGE a X hX i hi
  have hzero (n : ℕ) (y : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X)
      (hy : a ^ n • y = 0) : y = 0 := by
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      apply ih
      apply ha
      simpa only [pow_succ', mul_smul, smul_zero] using hy
  exact hzero n x hn

/-- 概要：主元局所化後に零になる加群の各元は、主元の冪で零になる。
方針：通常テンソルの局所化加群としての核判定を使う。
規約：ねじれ指数の一様性や有限生成性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化側のホモロジー消滅。 -/
theorem unconditionalModule_power_torsion_of_localization_isZero
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization.Away a B]
    (M : ModuleCat.{u} R)
    (h : IsZero ((ModuleCat.extendScalars (algebraMap R B)).obj M)) (x : M) :
    ∃ n : ℕ, a ^ n • x = 0 := by
  have hz : TensorProduct.mk R B M 1 x = 0 := by
    let e := extendScalarsObjEquivTensor R B M
    have := ModuleCat.isZero_iff_subsingleton.mp h
    have hs : Subsingleton (TensorProduct R B M) := e.symm.injective.subsingleton
    exact hs.elim _ _
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a)
    (TensorProduct.mk R B M 1)).mp hz
  obtain ⟨n, hn⟩ := s.property
  exact ⟨n, by simpa only [Submonoid.smul_def, ← hn] using hs⟩

/-- 概要：実局所化の負次数消滅から、元の負次数の各元冪ねじれ性を得る。
方針：平坦な実導来係数拡大のホモロジー比較と、通常局所化の核判定を使う。
規約：任意の実導来対象に適用する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化と完備化の合流。 -/
theorem unconditionalNegativeHomology_power_torsion_of_localization_isGE
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization.Away a B]
    (X : ConcreteDerivedCategory R)
    (h : ((flatDerivedBaseChange (algebraMap R B)
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B (Submonoid.powers a)))).obj X).IsGE 0)
    (i : ℤ) (hi : i < 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X) :
    ∃ n : ℕ, a ^ n • x = 0 := by
  let hφ : (algebraMap R B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B (Submonoid.powers a))
  let e := (flatDerivedBaseChangeHomologyNatIso (algebraMap R B) hφ i).app X
  have hz := (DerivedCategory.isGE_iff _ 0).mp h i hi
  exact unconditionalModule_power_torsion_of_localization_isZero a B _ (hz.of_iso e.symm) x

/-- 概要：完備化と主元局所化が負次数を持たなければ、元の対象も負次数を持たない。
方針：局所化から各元冪ねじれ性、完備化から同じ主元の単射性を得る。
規約：元の実対象に関する結論であり、有界性・完備性・正則性を追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 源の純性判定。 -/
theorem unconditional_isGE_of_completion_isGE_of_localization_isGE
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization.Away a B]
    (X : ConcreteDerivedCategory R)
    (hc : ((derivedComplexCompletionFunctor R a).obj X).IsGE 0)
    (hl : ((flatDerivedBaseChange (algebraMap R B)
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat B (Submonoid.powers a)))).obj X).IsGE 0) :
    X.IsGE 0 :=
  unconditional_isGE_of_completion_isGE_of_negative_power_torsion a X hc
    (unconditionalNegativeHomology_power_torsion_of_localization_isGE a B X hl)

end SerrePositivity.BhattScholze.Andre

end CompletionTorsionDetection

/-! ## 安定局所化の核と mod p の分母冪ねじれ

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の局所化側の消滅を、元の p 錐の分母冪ねじれへ移す。

## 方針
通常局所化の核判定と平坦導来ホモロジー比較を使う。
mod p で安定分母の像は元の分母の冪集合に等しい。

## 規約
指数は各元ごとに異なってよい。対象の完備性や有界ねじれは不要。

## 使われ方
元の raw 源の p 錐の完備化純性と合流する。
-/

@[expose] public noncomputable section SaturatedLocalizationTorsion

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- 概要：局所化後に零の通常加群では、各元が一つの分母で零になる。
方針：標準係数拡大を加群局所化へ比較し、その核判定を使う。
規約：分母集合は任意の乗法集合。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化側の実ホモロジー。 -/
theorem unconditionalModule_submonoid_torsion_of_localization_isZero
    {R : Type u} [CommRing R] (T : Submonoid R)
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization T B]
    (M : ModuleCat.{u} R)
    (h : IsZero ((ModuleCat.extendScalars (algebraMap R B)).obj M)) (x : M) :
    ∃ s : T, (s : R) • x = 0 := by
  have hz : TensorProduct.mk R B M 1 x = 0 := by
    let e := extendScalarsObjEquivTensor R B M
    have := ModuleCat.isZero_iff_subsingleton.mp h
    have hs : Subsingleton (TensorProduct R B M) := e.symm.injective.subsingleton
    exact hs.elim _ _
  exact (IsLocalizedModule.eq_zero_iff T (TensorProduct.mk R B M 1)).mp hz

/-- 概要：実導来局所化後のホモロジー消滅は、元の各元を一つの分母で零にする。
方針：平坦導来係数拡大の実ホモロジー比較を通常の局所化核判定へ渡す。
規約：元の上に有界な実導来対象を用いる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の raw 源の局所化核。 -/
theorem unconditionalHomology_submonoid_torsion_of_localization_isZero
    {R : Type u} [CommRing R] (T : Submonoid R)
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization T B]
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj X).obj))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj) :
    ∃ s : T, (s : R) • x = 0 := by
  let hφ : (algebraMap R B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B T)
  let e := (DerivedCategory.homologyFunctor (ModuleCat B) i).mapIso
      ((boundedAboveFlatDerivedBaseChangeIso (algebraMap R B) hφ).app X) ≪≫
    (flatDerivedBaseChangeHomologyNatIso (algebraMap R B) hφ i).app X.obj
  exact unconditionalModule_submonoid_torsion_of_localization_isZero T B _
    (h.of_iso e.symm) x

/-- 概要：p で零になる加群では、安定分母で零になる各元は元の分母の冪で零になる。
方針：安定分母の mod p 像を冪集合へ同定し、差が p の倍であることを使う。
規約：係数環の p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の実 p 錐の分母冪ねじれ。 -/
theorem unconditionalSaturatedTorsion_power_torsion_mod_prime
    {p : ℕ} [Fact p.Prime] {A R : Type u} [CommRing A] [CommRing R]
    (D : DeltaStructure p A) (d : A) (c : A →+* R)
    (M : ModuleCat.{u} R) (hp : ∀ x : M, (p : R) • x = 0) (x : M)
    (ht : ∃ s : (D.frobeniusDenominators (Submonoid.powers d)).map c.toMonoidHom,
      (s : R) • x = 0) : ∃ n : ℕ, (c d) ^ n • x = 0 := by
  obtain ⟨s, hs⟩ := ht
  obtain ⟨r, hr, hrs⟩ := s.property
  change c r = (s : R) at hrs
  rw [← hrs] at hs
  let q := Ideal.Quotient.mk (Ideal.span {(p : R)})
  have hpc : (q.comp c) (p : A) = 0 := by
    rw [RingHom.comp_apply, map_natCast]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hm : q (c r) ∈ Submonoid.powers (q (c d)) := by
    change (q.comp c) r ∈ Submonoid.powers ((q.comp c) d)
    rw [← unconditionalFrobeniusDenominators_map_mod_prime D d (q.comp c) hpc]
    exact ⟨r, hr, rfl⟩
  obtain ⟨n, hn⟩ := hm
  change (q (c d)) ^ n = q (c r) at hn
  have hdiff : (c d) ^ n - c r ∈ Ideal.span {(p : R)} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q ((c d) ^ n - c r) = 0
    rw [map_sub, map_pow, hn, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hdiff
  have hz : ((c d) ^ n - c r) • x = 0 := by
    rw [ht, mul_smul, smul_comm (p : R) t x, hp x, smul_zero]
  exact ⟨n, by simpa only [sub_smul, hs, sub_zero] using hz⟩

/-- 概要：実 p 錐が安定局所化後の指定次数で消えるなら、元の各元は分母冪ねじれ。
方針：局所化核と p 錐の p 零化を合成する。
規約：元の上に有界な実対象と標準係数射を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的源の局所化検出。 -/
theorem unconditionalSaturatedScalarCone_homology_power_torsion
    {p : ℕ} [Fact p.Prime] {A R : Type u} [CommRing A] [CommRing R]
    (D : DeltaStructure p A) (d : A) (c : A →+* R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (B : Type u) [CommRing B] [Algebra R B]
    [IsLocalization ((D.frobeniusDenominators (Submonoid.powers d)).map c.toMonoidHom) B]
    (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        ((boundedAboveDerivedScalarCone R (p : R)).obj X)).obj))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R (p : R)).obj X.obj)) :
    ∃ n : ℕ, (c d) ^ n • x = 0 := by
  let Y := (boundedAboveDerivedScalarCone R (p : R)).obj X
  have ht := unconditionalHomology_submonoid_torsion_of_localization_isZero
    ((D.frobeniusDenominators (Submonoid.powers d)).map c.toMonoidHom) B Y i h x
  exact unconditionalSaturatedTorsion_power_torsion_mod_prime D d c
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj Y.obj)
    (derivedScalarCone_homology_annihilated R (p : R) X.obj i) x ht

end SerrePositivity.BhattScholze.Andre

end SaturatedLocalizationTorsion

/-! ## 元の実源の p 錐の分母冪ねじれ

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の実源の p 錐の非零次ホモロジーは、分母冪ねじれ。

## 方針
元の安定係数局所化後の p 錐の純性と、p 錐ホモロジー上で p が零であることを使う。

## 規約
元の実二因子導来源を用い、prism 商の p 正則性を要求しない。

## 使われ方
完備化側の純性と合わせて、元の raw 源の p 正則性を検出する。
-/

@[expose] public noncomputable section SourcePrimeConeTorsion

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "LA" => RelativeFreeDeltaRing (R := A) σ
local notation "XA" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule (deltaDivisionSourceEval D a)),
    boundedAboveDerivedSingleFunctor.obj
      (baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)))
attribute [local instance] MvPolynomial.algebraMvPolynomial

set_option maxHeartbeats 800000 in
-- 元の二つの実係数作用と、同じ源の実 p 錐・局所化モデルを同時に照合するため。
set_option backward.isDefEq.respectTransparency true in
/-- 概要：元の実源の先行 p 錐の各非零次ホモロジー元は、元の分母の冪で零になる。
方針：実安定局所化の消滅を核判定へ渡し、p 錐上の p 零化で元の分母冪へ戻す。
規約：係数環上の p 正則性だけを仮定し、モニック性・完備性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の源の完備化純性との合流。 -/
theorem unconditionalSourcePrimeCone_homology_power_torsion
    (hp : IsSMulRegular A (p : A)) (i : ℤ) (hi : i ≠ 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat LA) i).obj
      ((derivedScalarConeFunctor LA (p : LA)).obj (XA).obj)) :
    ∃ n : ℕ, (MvPolynomial.C d : LA) ^ n • x = 0 := by
  let T := D.frobeniusDenominators (Submonoid.powers d)
  let B := Localization T
  let LB := RelativeFreeDeltaRing (R := B) σ
  letI : IsLocalization ((T).map (MvPolynomial.C : A →+* LA).toMonoidHom) LB := by
    change IsLocalization ((T).map (MvPolynomial.C : A →+* LA)) LB
    exact MvPolynomial.isLocalization T B
  exact (unconditionalSaturatedScalarCone_homology_power_torsion (R := LA)
    D d MvPolynomial.C XA LB i
    (unconditionalDeltaSourcePrimeCone_localization_homology_isZero D d a B hp i hi) x)

end SerrePositivity.BhattScholze.Andre

end SourcePrimeConeTorsion

/-! ## 元のスカラー錐と係数制限

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の源の p 錐の冪ねじれ性を、元の基底作用へ移す。

## 方針
任意の実複体モデル上の係数制限とスカラー錐の比較を導来圏へ運ぶ。

## 規約
環射の平坦性・単射性を要求しない。

## 使われ方
自由 δ 源上の局所化計算と、元の prism 基底上の完備化純性を合流する。
-/

@[expose] public noncomputable section ScalarConeRestriction

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- 概要：元の実スカラー錐と正確な係数制限は可換。
方針：同じ実複体モデル上の標準写像錐比較を使う。
規約：元のスカラーの像を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の源の p 錐の標準基底作用。 -/
def unconditionalRestrictionScalarConeIso (a : R) (X : ConcreteDerivedCategory S) :
    (derivedScalarConeFunctor R a).obj ((derivedRestrictScalars φ).obj X) ≅
      (derivedRestrictScalars φ).obj ((derivedScalarConeFunctor S (φ a)).obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let eX := DerivedCategory.Q.objObjPreimageIso X
  let KR := ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K
  exact (derivedScalarConeFunctor R a).mapIso
      ((derivedRestrictScalars φ).mapIso eX.symm ≪≫ (derivedRestrictScalarsFactors φ).app K) ≪≫
    (derivedScalarConeComparison R a).app KR ≪≫
    DerivedCategory.Q.mapIso (restrictionScalarConeIso φ a (φ a) rfl K).symm ≪≫
    ((derivedRestrictScalarsFactors φ).app ((scalarConeFunctor (φ a)).obj K)).symm ≪≫
    (derivedRestrictScalars φ).mapIso
      ((derivedScalarConeComparison S (φ a)).symm.app K ≪≫
        (derivedScalarConeFunctor S (φ a)).mapIso eX)

/-- 概要：元の実スカラー錐の冪ねじれ性は、同じ基底元の係数制限へ移る。
方針：実錐比較とホモロジー係数制限の線形同型を使う。
規約：指数は元ごとに異なってよい。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の局所化計算の元の A 作用への移送。 -/
theorem unconditionalRestrictionScalarCone_homology_power_torsion
    (a d : R) (X : ConcreteDerivedCategory S) (i : ℤ)
    (ht : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((derivedScalarConeFunctor S (φ a)).obj X), ∃ n : ℕ, (φ d) ^ n • x = 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj ((derivedRestrictScalars φ).obj X))) :
    ∃ n : ℕ, d ^ n • x = 0 := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      (unconditionalRestrictionScalarConeIso φ a X) ≪≫
    (derivedRestrictScalarsHomologyIso φ i).app ((derivedScalarConeFunctor S (φ a)).obj X)
  let y : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
    ((derivedScalarConeFunctor S (φ a)).obj X) := e.hom x
  obtain ⟨n, hn⟩ := ht y
  refine ⟨n, e.toLinearEquiv.injective ?_⟩
  rw [e.toLinearEquiv.map_smul, e.toLinearEquiv.map_zero]
  change φ (d ^ n) • y = 0
  rw [map_pow]
  exact hn

/-- 概要：同じ冪ねじれの移送を、元の上に有界な係数制限対象で述べる。
方針：標準の包含比較と実ホモロジー同型で前の判定を移す。
規約：元の boundedAboveDerivedRestrictScalars を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的な実源の型の照合。 -/
theorem unconditionalBoundedRestrictionScalarCone_homology_power_torsion
    (a d : R) (X : DerivedCategory.Minus (ModuleCat.{u} S)) (i : ℤ)
    (ht : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((derivedScalarConeFunctor S (φ a)).obj X.obj), ∃ n : ℕ, (φ d) ^ n • x = 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj ((boundedAboveDerivedRestrictScalars φ).obj X).obj)) :
    ∃ n : ℕ, d ^ n • x = 0 := by
  let eI := (boundedAboveDerivedRestrictScalarsInclusionIso φ).app X
  let eH := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
    ((derivedScalarConeFunctor R a).mapIso eI)
  obtain ⟨n, hn⟩ := unconditionalRestrictionScalarCone_homology_power_torsion
    φ a d X.obj i ht (eH.hom x)
  refine ⟨n, eH.toLinearEquiv.injective ?_⟩
  rw [eH.toLinearEquiv.map_smul, eH.toLinearEquiv.map_zero]
  exact hn

end SerrePositivity.BhattScholze.Andre

end ScalarConeRestriction
