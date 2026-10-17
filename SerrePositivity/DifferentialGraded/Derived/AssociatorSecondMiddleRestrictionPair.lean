module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionNested
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionPresentation

/-! # 第二中間制限と全導来結合子の二段階合成側のモデルsquare -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E)
  (hD : localHomKFlat A D) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)
  (S : RightKFlatBimoduleCategory A D T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj)
  (hq : BimoduleCategory.quasiIso A D T q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "L" => derivedBimoduleRestriction A B D B E (DGFunctor.id B) F
local notation "RRD" => Functor.obj
  (derivedBimoduleRestriction A D T E T F (DGFunctor.id T)) RT
local notation "HD" => derivedBimoduleComposeFunctor A B D T hT
local notation "eS" => middleRestrictionKFlatFactorIso A E D T F R S q hq
local notation "aQIso" => Iso.app
  (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD) Q
local notation "sIso" => Iso.trans (Functor.mapIso HD eS)
  (derivedBimoduleComposeKFlatIso A B D T hT S)

/-- 二段階合成の表示は、前の因子の表示を先に行う順序へ自然性で正規化できる。 -/
lemma derivedSecondMiddleRestriction_pair_comparison_hom :
    (derivedBimoduleComposePairComparisonIso A B C D T hD hT LQ S
        ((middleLeftRestrictionDerivedIso A C E D F).app Q.obj).symm eS).hom =
    whiskerRight (aQIso).hom ((HD).obj RRD) ≫
      whiskerLeft (rightKFlatDerivedCompose A B C D LQ) (sIso).hom := by
  apply NatTrans.ext
  funext P
  have hn := ((HD).map (eS).hom).naturality
    ((derivedBimoduleComposeKFlatIso A B C D hD LQ).hom.app P)
  simp only [derivedBimoduleComposePairComparisonIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    leftRestrictionDerivedComposeTargetBaseIso_hom_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

private lemma paste_horizontal {V W X : Type*} [Category* V] [Category* W] [Category* X]
    (U : W ⥤ V) (H K : V ⥤ X) (J M : W ⥤ X)
    (b : U ⋙ H ⟶ J) (b' : U ⋙ K ⟶ M) (k : H ⟶ K) (l : J ⟶ M)
    (hb : b ≫ l = whiskerLeft U k ≫ b')
    {x x' : V} {y y' : W} (a : x ⟶ U.obj y) (v : y ⟶ y')
    (w : x ⟶ x') (a' : x' ⟶ U.obj y') (ha : a ≫ U.map v = w ≫ a') :
    H.map a ≫ b.app y ≫ J.map v ≫ l.app y' =
      H.map w ≫ k.app x' ≫ K.map a' ≫ b'.app y' := by
  have hn := b.naturality v
  have hm := congrArg H.map ha
  have hc := NatTrans.congr_app hb y'
  simp only [Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.map_comp] at hm
  simp only [NatTrans.comp_app, whiskerLeft_app] at hc
  calc
    _ = H.map a ≫ H.map (U.map v) ≫ b.app y' ≫ l.app y' := by rw [← reassoc_of% hn]
    _ = H.map w ≫ H.map a' ≫ b.app y' ≫ l.app y' := by
      rw [← Category.assoc (H.map a), hm, Category.assoc]
    _ = H.map w ≫ H.map a' ≫ k.app (U.obj y') ≫ b'.app y' := by rw [hc]
    _ = _ := by rw [← reassoc_of% (k.naturality a')]

/-- 二段階の実際の外側左比較・中間比較は、指定K-flatモデルの二段階比較に戻る。 -/
lemma derivedSecondMiddleRestriction_pair_model_square (hE : localHomKFlat A E) :
    whiskerRight
        ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app QT)
        ((HD).obj RRD) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedMiddleRestrictionNatTrans A B E D T F hT).app RT) ≫
      (derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    (derivedBimoduleComposePairComparisonIso A B C D T hD hT LQ S
        ((middleLeftRestrictionDerivedIso A C E D F).app Q.obj).symm eS).hom ≫
      whiskerRight (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom
        (rightKFlatDerivedCompose A B D T S) ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatMiddleComparison A B E D T F R S q) := by
  have ha := derivedBimoduleComposeLeftRestrictionIso_inv_model_square A B C E D F hE hD Q
  rw [leftRestrictionDerivedComposeSourceBaseIso_hom_app] at ha
  have hb := derivedMiddleRestrictionNatTrans_kFlat_model_calculation A B E D T F hT R S q hq
  rw [middleRestrictionKFlatSourceIso_hom] at hb
  rw [derivedSecondMiddleRestriction_pair_comparison_hom]
  apply NatTrans.ext
  funext P
  have hc := NatTrans.congr_app ha P
  simp only [NatTrans.comp_app, whiskerRight_app] at hc
  have h := paste_horizontal L _ _ _ _ _ _ (sIso).hom _ hb _ _ _ _ hc
  convert h using 1 <;>
    simp only [derivedBimoduleComposePairComparisonIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.Functor.map_id,
      whiskerLeft_id', whiskerRight_id', NatTrans.comp_app, whiskerLeft_app,
      whiskerRight_app, Category.id_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
