module

public import SerrePositivity.BhattScholze.Andre.Unconditional.FreeCoefficientSquare
public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootQuotientDerived

/-!
# 元の A 係数における無限根源の実 (p,d) 還元

## 概要
BS Rem 7.15（著者版 p.62）の元の無限根モニック源について、
A/(p,d) に沿う実導来還元を、同じ raw 残余商の single 対象へ同定する。

## 方針
自由な無限根環と自由 δ 環の A 自由性で導来係数商の正方形を比較し、
全残余源の hpR なしの Koszul・Tor 計算を用いる。

## 規約
元の A 係数作用を保持し、raw 包をねじれ除去商へ変更しない。

## 使われ方
元の実逐次完備化の生成元冪商の有界ねじれ・純性による hpR 解消へ渡す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P₀" => PowerRootPolynomial A p hp
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "C₀" => algebraMap A L₀
local notation "dP" => algebraMap A P₀ W.generator
local notation "I₀" => Ideal.span {(p : A), W.generator}
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C dP}
local notation "Q₀" => L₀ ⧸ K₀
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk K₀

/-- 概要：元の係数イデアル (p,d) の拡張は無限根自由 δ 源の実 (p,dP) イデアル。
方針：二元生成イデアルの像と係数射の定義を計算する。
規約：prism の完全性も hpR も不要。
使われ方：BS Rem 7.15（著者版 p.62）の係数還元の正確な型の照合。 -/
theorem powerRootSourcePDIdeal_map_of_unconditional : (I₀).map C₀ = K₀ := by
  rw [Ideal.map_span, Set.image_pair, map_natCast]
  rfl

/-- 概要：A/(p,d) から元の自由 δ 源の実残余商への標準係数射。
方針：拡張イデアルの等式で元の A 係数射を商へ降下する。
規約：元の全係数の像を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の実残余商の元の基底作用。 -/
def powerRootSourceQuotientCoefficientMap_of_unconditional : R₀ →+* Q₀ :=
  Ideal.quotientMap K₀ C₀ (by
    rw [← powerRootSourcePDIdeal_map_of_unconditional W]
    exact Ideal.le_comap_map)
local notation "κ₀" => powerRootSourceQuotientCoefficientMap_of_unconditional W

/-- 概要：元の A/(p,d) 導来還元と実自由 δ 源商の導来還元の係数制限は同型。
方針：自由な係数代数の一般正方形比較を拡張イデアルの等式で移す。
規約：実導来対象と射影モデルだけを引数にし、hpR を追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の A 作用に沿う実剰余比較。 -/
def powerRootSourcePDDerivedSquareIso_of_unconditional
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (M : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj
        ((boundedAboveDerivedBaseChange q₀).obj X) := by
  let : Module.Free A P₀ := inferInstance
  let : Module.Free A L₀ := Module.Free.trans (R := A) (S := P₀) (M := L₀)
  let F (J : Ideal L₀) :=
    Σ' h : I₀ ≤ J.comap C₀,
      letI := Ideal.Quotient.algebraQuotientOfLEComap h
      (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
          ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
        (boundedAboveDerivedRestrictScalars (algebraMap (A ⧸ I₀) (L₀ ⧸ J))).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J)).obj X)
  let e : F ((I₀).map C₀) :=
    ⟨Ideal.le_comap_map, freeCoefficientDerivedSquareIso I₀ X M⟩
  let e' : F K₀ := Eq.mp
    (congrArg F (powerRootSourcePDIdeal_map_of_unconditional W)) e
  letI := Ideal.Quotient.algebraQuotientOfLEComap e'.1
  have hκ : algebraMap (A ⧸ I₀) Q₀ = κ₀ := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    rfl
  simpa only [hκ] using e'.2

variable (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "E₀" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "c₀" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "α₀" => deltaDivisionSourceMap E₀ dP
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "X₀" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ dP c₀
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)
local notation "LCoef" => C₀

/-- 概要：一般モニック f/d 包の実二因子導来対象を元の係数環 A へ制限する。
方針：二重多項式係数包含に沿う既存の導来係数制限を適用する。
規約：有限性やモニック性は対象の定義には不要。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数環上の実 prismatic 源。 -/
abbrev PowerRootPrismMonicSourceCoefficientObject_of_unconditional :=
  (boundedAboveDerivedRestrictScalars LCoef).obj X₀

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
-- 実二因子の具体的な射影テンソルモデルと二重係数商の作用を同時に照合するため。
/-- 概要：元の A/(p,d) に沿う実還元は、実自由 δ 源商上の還元の係数制限と同型。
方針：二重多項式源に対する既存の一般導来係数正方形比較を再利用する。
規約：正方形比較自体にはモニック性も有限性も不要。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余の元の係数作用への比較。 -/
def powerRootPrismMonicSourceCoefficientPDReductionIso_of_unconditional :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj
        (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f) := by
  with_reducible exact (powerRootSourcePDDerivedSquareIso_of_unconditional W X₀
    (boundedAboveDerivedTensorModel
      (boundedAboveDerivedSingleFunctor.obj Mβ) (boundedAboveDerivedSingleFunctor.obj Mα)))

local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀))
  (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f)

/-- 概要：元のA上の実モニック族添加対象の実(p,d)還元と、作用を制限したraw商のsingle比較。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：完全 prism とモニック性のみを使う。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
def powerRootPrismMonicSourceCoefficientPDResidueIso_of_unconditional (hf : f.Monic) :
    letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Y₀ ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact powerRootPrismMonicSourceCoefficientPDReductionIso_of_unconditional W hW f ≪≫
    (boundedAboveDerivedRestrictScalars κ₀).mapIso
      (powerRootPrismMonicSourceQuotientDerivedSingleIso_of_unconditional W hW f hf) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso κ₀ 0).app (ModuleCat.of Q₀ Res₀))

/-- 概要：元のA上の実還元のH0と、標準係数作用を制限したraw商の加群同型。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：完全 prism とモニック性のみを使う。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
def powerRootPrismMonicSourceCoefficientPDResidueH0Iso_of_unconditional (hf : f.Monic) :
    letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅ MRes := by
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceCoefficientPDResidueIso_of_unconditional W hW f hf)) ≪≫
    (realizedSingleH0Iso R₀).app MRes

/-- 概要：元のA上の実(p,d)還元の非零次数ホモロジーは零。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：完全 prism とモニック性のみを使う。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
theorem powerRootPrismMonicSourceCoefficientPDResidue_homology_isZero_of_unconditional
    (hf : f.Monic)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Y₀).obj) := by
  let := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceCoefficientPDResidueIso_of_unconditional W hW f hf)))


end SerrePositivity.BhattScholze.Andre
