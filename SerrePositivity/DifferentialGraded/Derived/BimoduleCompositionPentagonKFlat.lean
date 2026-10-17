module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonShort

/-! # 全導来五角図式の長経路とK-flat三因子の比較

## 概要
全導来五角図式の長経路とK-flat三因子の比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionFamilies.lean。
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

def derivedBimoduleTripleSourceAltIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R.obj) ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj) ≅
      rightKFlatDerivedCompose A B C E Q ⋙ rightKFlatDerivedCompose A B E F R ⋙
        rightKFlatDerivedCompose A B F G S :=
  isoWhiskerRight
      (isoWhiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q)
          ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R.obj)) ≪≫
        isoWhiskerLeft (rightKFlatDerivedCompose A B C E Q)
          (derivedBimoduleComposeKFlatIso A B E F hF R))
      ((derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj)) ≪≫
    isoWhiskerLeft (rightKFlatDerivedCompose A B C E Q ⋙ rightKFlatDerivedCompose A B E F R)
      (derivedBimoduleComposeKFlatIso A B F G hG S)

lemma derivedBimoduleTripleSourceAltIso_eq (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    derivedBimoduleTripleSourceAltIso A B C E F G hE hF hG Q R S =
      derivedBimoduleTripleSourceIso A B C E F G hE hF hG Q R S := by
  apply Iso.ext
  ext P
  have hr := (derivedBimoduleComposeKFlatIso A B E F hF R).hom.naturality
    ((derivedBimoduleComposeKFlatIso A B C E hE Q).hom.app P)
  have hm := congrArg
    ((derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj)).map hr
  simp only [CategoryTheory.Functor.map_comp] at hm
  have hs := (derivedBimoduleComposeKFlatIso A B F G hG S).hom.naturality
    ((rightKFlatDerivedCompose A B E F R).map
      ((derivedBimoduleComposeKFlatIso A B C E hE Q).hom.app P))
  simp only [derivedBimoduleTripleSourceAltIso, derivedBimoduleTripleSourceIso,
    Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, CategoryTheory.Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map, rightKFlatDerivedCompose] at hm hs ⊢
  rw [reassoc_of% hm, hs]

lemma derivedBimodulePentagonLong_middle (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    whiskerRight (derivedBimoduleAssociator A B C E F hE hF
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)).hom
      ((derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj)) ≫
      (derivedBimoduleComposePairComparisonIso A B C F G hF hG (rightKFlatCompose A C E F Q R)
        S (derivedBimoduleComposeKFlatValueIso A C E F hF R Q.obj) (Iso.refl _)).hom =
    (derivedBimoduleTripleSourceIso A B C E F G hE hF hG Q R S).hom ≫
      whiskerRight (rightKFlatDerivedAssociator A B C E F Q R).hom
        (rightKFlatDerivedCompose A B F G S) := by
  rw [← derivedBimoduleTripleSourceAltIso_eq]
  ext P
  have ha := NatTrans.congr_app
    (derivedBimoduleAssociatorIso_kFlat_fac A B C E F hE hF Q R) P
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at ha
  change (derivedBimoduleAssociator A B C E F hE hF _ _).hom.app P ≫ _ = _ at ha
  have hm := congrArg
    ((derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj)).map ha
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hm
  have hs := (derivedBimoduleComposeKFlatIso A B F G hG S).hom.naturality
    ((rightKFlatDerivedAssociator A B C E F Q R).hom.app P)
  simp only [derivedBimoduleComposePairComparisonIso, derivedBimoduleTripleSourceAltIso,
    Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.refl_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_id, whiskerLeft_id',
    Category.id_comp, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hm, hs]

lemma derivedBimodulePentagonLong_kFlat_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    derivedBimodulePentagonLong A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj) ≫
      (derivedBimoduleTripleRightFunctorIso A B C E F G hG Q R S).hom =
    (derivedBimoduleTripleSourceIso A B C E F G hE hF hG Q R S).hom ≫
      whiskerRight (rightKFlatDerivedAssociator A B C E F Q R).hom
        (rightKFlatDerivedCompose A B F G S) ≫
      (rightKFlatDerivedAssociator A B C F G (rightKFlatCompose A C E F Q R) S).hom ≫
      rightKFlatDerivedMap A B C G
        (Q := rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S)
        (Q' := rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S))
        (associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
          (BimoduleCategory.underlying A E F R.obj)
          (BimoduleCategory.underlying A F G S.obj)).hom := by
  have h := derivedBimoduleAssociator_comparison_fac A B C F G hF hG
    (rightKFlatCompose A C E F Q R) S
    (derivedBimoduleComposeKFlatValueIso A C E F hF R Q.obj) (Iso.refl _)
  change (derivedBimoduleAssociator A B C F G hF hG _ _).hom ≫
    (derivedBimoduleTripleLeftFunctorIso A B C E F G hF hG Q R S).hom = _ at h
  change (_ ≫ (_ ≫ _)) ≫ _ = _
  simp only [Category.assoc]
  rw [derivedBimoduleTripleFunctorIso_associator]
  rw [reassoc_of% h]
  rw [← Category.assoc, derivedBimodulePentagonLong_middle, Category.assoc]

lemma derivedBimodulePentagon_kFlat (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    derivedBimodulePentagonShort A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj) =
      derivedBimodulePentagonLong A B C E F G hE hF hG
        ((bimoduleToDerived A C E).obj Q.obj) ((bimoduleToDerived A E F).obj R.obj)
        ((bimoduleToDerived A F G).obj S.obj) := by
  apply (Iso.cancel_iso_hom_right _ _
    (derivedBimoduleTripleRightFunctorIso A B C E F G hG Q R S)).1
  rw [derivedBimodulePentagonShort_kFlat_fac, derivedBimodulePentagonLong_kFlat_fac,
    derivedPentagon]

end SerrePositivity.DifferentialGraded.BimoduleTensor
