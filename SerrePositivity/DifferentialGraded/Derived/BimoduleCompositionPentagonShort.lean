module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonComparison

/-! # 全導来五角図式の短経路のK-flat比較

## 概要
全導来五角図式の短経路のK-flat比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonKFlat.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

lemma derivedBimodulePentagonShort_middle (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj Q.obj))
      (derivedBimoduleAssociator A B E F G hF hG
        ((bimoduleToDerived A E F).obj R.obj) ((bimoduleToDerived A F G).obj S.obj)).hom ≫
      (derivedBimoduleComposePairComparisonIso A B C E G hE hG Q
        (rightKFlatCompose A E F G R S) (Iso.refl _)
        (derivedBimoduleComposeKFlatValueIso A E F G hG S R.obj)).hom =
    (derivedBimoduleTripleSourceIso A B C E F G hE hF hG Q R S).hom ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatDerivedAssociator A B E F G R S).hom := by
  ext P
  let FQ := (derivedBimoduleComposeFunctor A B C E hE).obj
    ((bimoduleToDerived A C E).obj Q.obj)
  let KQ := rightKFlatDerivedCompose A B C E Q
  let c := (derivedBimoduleComposeKFlatIso A B C E hE Q).hom.app P
  let RS := rightKFlatCompose A E F G R S
  have hx := (derivedBimoduleComposeKFlatIso A B E G hG RS).hom.naturality c
  have hy := (rightKFlatDerivedAssociator A B E F G R S).hom.naturality c
  have ha := NatTrans.congr_app
    (derivedBimoduleAssociatorIso_kFlat_fac A B E F G hF hG R S) (FQ.obj P)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at ha
  change (derivedBimoduleAssociator A B E F G hF hG
      ((bimoduleToDerived A E F).obj R.obj) ((bimoduleToDerived A F G).obj S.obj)).hom.app
        (FQ.obj P) ≫ _ = _ at ha
  simp only [derivedBimoduleComposePairComparisonIso, derivedBimoduleTripleSourceIso,
    Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.refl_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_id,
    whiskerRight_id', Category.id_comp, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  simp only [Category.assoc] at ha ⊢
  rw [hx]
  simp only [← Category.assoc] at ha ⊢
  rw [ha]
  simp only [Category.assoc]
  rw [← hy]

lemma derivedBimodulePentagonShort_kFlat_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    derivedBimodulePentagonShort A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj) ≫
      (derivedBimoduleTripleRightFunctorIso A B C E F G hG Q R S).hom =
    (derivedBimoduleTripleSourceIso A B C E F G hE hF hG Q R S).hom ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatDerivedAssociator A B E F G R S).hom ≫
      (rightKFlatDerivedAssociator A B C E G Q (rightKFlatCompose A E F G R S)).hom := by
  have h := derivedBimoduleAssociator_comparison_fac A B C E G hE hG Q
    (rightKFlatCompose A E F G R S) (Iso.refl _)
    (derivedBimoduleComposeKFlatValueIso A E F G hG S R.obj)
  change (derivedBimoduleAssociator A B C E G hE hG _ _).hom ≫
    (derivedBimoduleTripleRightFunctorIso A B C E F G hG Q R S).hom = _ at h
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc, h, ← Category.assoc, derivedBimodulePentagonShort_middle, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
