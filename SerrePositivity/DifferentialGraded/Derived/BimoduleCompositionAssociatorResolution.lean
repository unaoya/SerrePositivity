module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPairResolution

/-! # 指定K-flat解像度による全導来合成の結合比較

## 概要
指定K-flat解像度による全導来合成の結合比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorNaturality.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

/-- 最初の導来変数全体に自然な結合比較。後二因子には指定した解像度を使う。 -/
def derivedBimoduleAssociatorResolutionIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R) ≅
      (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj
          ((bimoduleToDerived A E F).obj R)).obj ((bimoduleToDerived A C E).obj Q)) :=
  derivedBimoduleComposePairResolutionIso A B C E F hE hF Q R S T q r hq hr ≪≫
    rightKFlatDerivedAssociator A B C E F S T ≪≫
    (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q R S T q r hq hr).symm

/-- 全導来結合比較を解像度で計算すると、既存K-flat結合比較の図式に戻る。 -/
lemma derivedBimoduleAssociatorResolutionIso_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom ≫
        (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q R S T q r hq hr).hom =
      (derivedBimoduleComposePairResolutionIso A B C E F hE hF Q R S T q r hq hr).hom ≫
        (rightKFlatDerivedAssociator A B C E F S T).hom := by
  change (_ ≫ (_ ≫ _)) ≫ _ = _
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma derivedBimoduleAssociatorResolutionIso_base_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r)
    (P : BimoduleCategory A B C) :
    (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q R S T q r hq hr).hom.app
        ((bimoduleToDerived A B C).obj P) =
    (derivedBimoduleComposePairResolutionIso A B C E F hE hF Q R S T q r hq hr).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (bimoduleToDerived A B F).map
        (associatorIso A B C E F (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E S.obj)
          (BimoduleCategory.underlying A E F T.obj)).hom := by
  have h := NatTrans.congr_app
    (derivedBimoduleAssociatorResolutionIso_fac A B C E F hE hF Q R S T q r hq hr)
    ((bimoduleToDerived A B C).obj P)
  simp only [NatTrans.comp_app, rightKFlatDerivedAssociator_base_app] at h
  exact h

/-- 後二因子の標準解像度を使った結合比較。選択独立性・後因子自然性は別途必要。 -/
def derivedBimoduleAssociatorBaseIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R) ≅
      (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj
          ((bimoduleToDerived A E F).obj R)).obj ((bimoduleToDerived A C E).obj Q)) :=
  derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R
    (rightKFlatResolutionObj A C E hE Q) (rightKFlatResolutionObj A E F hF R)
    (bimoduleCanonicalSemifreeResolution A C E Q).π
    (bimoduleCanonicalSemifreeResolution A E F R).π
    (bimoduleCanonicalSemifreeResolution A C E Q).quasiIso
    (bimoduleCanonicalSemifreeResolution A E F R).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
