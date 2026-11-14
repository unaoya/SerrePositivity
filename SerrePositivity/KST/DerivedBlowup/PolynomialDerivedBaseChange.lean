module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.DerivedBlowup.PolynomialPushoutBaseChange
public import SerrePositivity.KST.DerivedBlowup.PolynomialKoszulKFlat
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension

/-!
概要：KST Lemma3.6 の普遍基底からの導来底変更を表示多項式環上の底変更へ比較する。
方針：基底上の K-flat 計算同型に、多項式 pushout の非有界複体比較を合成する。
規約：係数変更先の環の平坦性を仮定しない。
使われ方：普遍 blowup チャートの導来底変更の Koszul 計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w w'

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {I : Type}

/-- 概要：基底上で K-flat な多項式係数複体の導来底変更は表示環上の項別底変更で計算できる。
方針：実際の導来係数拡大の K-flat 計算と pushout の複体自然同型を合成する。
規約：KST Lemma3.6、任意の非有界複体。
使われ方：普遍 Koszul 解消の任意係数への導来底変更。 -/
def polynomialDerivedBaseChangeIso
    (K : CochainComplex (ModuleCat.{u} (MvPolynomial I A)) ℤ)
    (hK : DifferentialGraded.complexKFlat A
      (((ModuleCat.restrictScalars (algebraMap A (MvPolynomial I A))).mapHomologicalComplex
        (.up ℤ)).obj K))
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w'} (ModuleCat.{u} B)] :
    (DifferentialGraded.ScalarExtension.complexDerivedExtension (algebraMap A B)).obj
        (DerivedCategory.Q.obj (((ModuleCat.restrictScalars
          (algebraMap A (MvPolynomial I A))).mapHomologicalComplex (.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj (((ModuleCat.restrictScalars
        (algebraMap B (MvPolynomial I B))).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars (algebraMap (MvPolynomial I A)
            (MvPolynomial I B))).mapHomologicalComplex (.up ℤ)).obj K)) :=
  DifferentialGraded.ScalarExtension.complexDerivedExtensionKFlatIso (algebraMap A B) _ hK ≪≫
    DerivedCategory.Q.mapIso
      ((polynomialPushoutComplexNatIso (A := A) (B := B) (I := I)).app K).symm

/-- 概要：有限多項式 Koszul 複体の普遍基底上の導来底変更の具体的計算。
方針：基底へ係数制限した Koszul 複体の K-flat 性を一般比較へ渡す。
規約：KST Lemma3.6、関係式の正則性はこの底変更比較には不要。
使われ方：正則な普遍関係式の解消から任意係数の導来チャートを得る。 -/
def polynomialKoszulDerivedBaseChangeIso {n : ℕ} (x : Fin n → MvPolynomial I A)
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w'} (ModuleCat.{u} B)] :=
  polynomialDerivedBaseChangeIso (B := B) (sequenceExteriorCochain x)
    (polynomialKoszulRestriction_kFlat x)

end SerrePositivity.KST.DerivedBlowup

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Def 3.1" (partial := component) "仮定：多項式基底の普遍チャートと有限列（Lean が強い）。結論：チャート上の古典的商表示と Koszul の底変換の同型。全導来スキームの正方形は未接続（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.polynomialKoszulDerivedBaseChangeIso
attribute [cite KST "Eq (1.8)" (partial := component) "仮定：普遍多項式模型の指定チャートと有限列（Lean が強い）。結論：導来底変換の二種類の局所比較。通常・導来両側を含む全立方体は未接続（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.polynomialKoszulDerivedBaseChangeIso
attribute [cite KST "Eq (3.1)" (partial := component) "仮定：多項式基底の普遍チャートと有限列（Lean が強い）。結論：チャート上の古典的商表示と Koszul の底変換の同型。全導来スキームの正方形は未接続（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.polynomialKoszulDerivedBaseChangeIso
attribute [cite KST "Eq (3.2)" (partial := component) "仮定：係数環と多項式普遍模型の有限列（Lean が強い）。結論：導来底変換の Koszul 複体の比較。全導来スキームのブローアップ正方形の引き戻しは含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.polynomialKoszulDerivedBaseChangeIso
attribute [cite KST "Eq (5.11)" (partial := component) "仮定：通常ブローアップの整数冪、または指定された普遍 Koszul の底変換（Lean が強い）。結論：イデアルと冪の同型・局所 Koszul 比較。異なる冪列の有限射を導来ブローアップ間に構成する部分は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.polynomialKoszulDerivedBaseChangeIso
attribute [cite KST "Lemma 3.6" (partial := component) "仮定：普遍多項式模型からの指定された底変換（Lean が強い）。結論：係数環・例外因子上の明示的比較は得るが、任意の二つの正則列表示に対する正方形と全厚化の独立性は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.polynomialKoszulDerivedBaseChangeIso
attribute [cite LT "Eq (22)" (partial := component) "仮定：指定普遍多項式模型のチャートと係数環の有限列（Lean が強い）。結論：局所的な通常チャートと導来 Koszul の底変換を比較。全 qcqs スキームのブローアップ四角形は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.polynomialKoszulDerivedBaseChangeIso
attribute [cite LT "Eq (23)" (partial := component) "仮定：指定普遍多項式模型のチャートと係数環の有限列（Lean が強い）。結論：局所的な通常チャートと導来 Koszul の底変換を比較。全 qcqs スキームのブローアップ四角形は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.polynomialKoszulDerivedBaseChangeIso
