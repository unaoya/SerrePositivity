module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIdentity

/-! # dg関手の合成と指定モデルによる実際の導来中間比較の整合性

## 概要
dg関手の合成と指定モデルによる実際の導来中間比較の整合性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (L : Type s) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

lemma derivedBimoduleComposeResolutionValueIso_first_naturality
    (Q : BimoduleCategory A D L) (R : RightKFlatBimoduleCategory A D L)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A D L q)
    {P P' : BimoduleCategory A B D} (f : P ⟶ P') :
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj Q)).map
        ((bimoduleToDerived A B D).map f) ≫
      (derivedBimoduleComposeResolutionValueIso A B D L hL Q R q hq P').hom =
    (derivedBimoduleComposeResolutionValueIso A B D L hL Q R q hq P).hom ≫
      (bimoduleToDerived A B L).map (composeMap A B D L f (𝟙 R.obj)) := by
  change _ ≫ (_ ≫ 𝟙 _) = (_ ≫ 𝟙 _) ≫ _
  simp only [Category.comp_id]
  exact (derivedBimoduleComposeResolutionComputation A B D L hL Q R q hq).hom.naturality
    ((bimoduleToDerived A B D).map f)

lemma derivedBimoduleComposeResolutionValueIso_fac
    (Q : BimoduleCategory A D L) (R : RightKFlatBimoduleCategory A D L)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A D L q) (P : BimoduleCategory A B D) :
    ((derivedBimoduleComposeFunctor A B D L hL).map ((bimoduleToDerived A D L).map q)).app
        ((bimoduleToDerived A B D).obj P) ≫
      (derivedBimoduleComposeResolutionValueIso A B D L hL Q R q hq P).hom =
    (derivedBimoduleComposeKFlatValueIso A B D L hL R P).hom := by
  have h := NatTrans.congr_app
    (derivedBimoduleComposeResolutionComputation_fac A B D L hL Q R q hq)
    ((bimoduleToDerived A B D).obj P)
  change _ ≫ (_ ≫ 𝟙 _) = _
  rw [Category.comp_id]
  exact h

variable (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階比較のsourceを、合成関手による比較のsourceへ結ぶ自然な計算同型。 -/
def derivedMiddleCompositeSourceIso
    (P : BimoduleCategory A B T) (Q : BimoduleCategory A T L) (R : BimoduleCategory A E L)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q)
    (hq : BimoduleCategory.quasiIso A E L q) :
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≅
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B T D (F.comp G)).obj P)) :=
  ((derivedBimoduleComposeFunctor A B D L hL).mapIso
    (bimoduleDerivedIso A D L (BimoduleCategory.middleRightRestrictionCompositeMap A D E T L F G q)
      (BimoduleCategory.middleRightRestrictionCompositeMap_quasiIso A D E T L F G q hq))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≪≫
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q))).mapIso
      ((bimoduleToDerived A B D).mapIso
        (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P))

/-- 合成比較のsource同型は、同じ最終モデルによる導来合成の計算と可換。 -/
lemma derivedMiddleCompositeSourceIso_computation
    (P : BimoduleCategory A B T) (Q : RightKFlatBimoduleCategory A T L)
    (R : RightKFlatBimoduleCategory A E L) (S : RightKFlatBimoduleCategory A D L)
    (r : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
    (hr : BimoduleCategory.quasiIso A D L r) (hq : BimoduleCategory.quasiIso A E L q) :
    (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj q hq).hom ≫
        (middleRestrictionSourceComputation A B T D L (F.comp G) hL P Q.obj S
          (BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q)
          (BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
            A D E T L F G r q hr hq)).hom =
      (middleRestrictionSourceComputation A B E D L F hL
        ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) R.obj S r hr).hom ≫
        (bimoduleToDerived A B L).map
          (middleRestrictionCompSourceIso A B D E T L F G P S.obj).hom := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P
  let P₂ := (BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj P₀
  let k := BimoduleCategory.middleRightRestrictionCompositeMap A D E T L F G q
  let a := BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q
  have ha := BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
    A D E T L F G r q hr hq
  have h₀ := derivedBimoduleComposeResolutionValueIso_naturality A B D L hL S S r a hr ha
    k (𝟙 S) (by
      change (bimoduleToDerived A D L).map r ≫ (bimoduleToDerived A D L).map k =
        (bimoduleToDerived A D L).map (𝟙 S.obj) ≫ (bimoduleToDerived A D L).map a
      rw [CategoryTheory.Functor.map_id, Category.id_comp, ← CategoryTheory.Functor.map_comp]
      rfl) P₂
  change _ = (derivedBimoduleComposeResolutionValueIso A B D L hL
    ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj) S r hr P₂).hom ≫
      (bimoduleToDerived A B L).map (composeMap A B D L (𝟙 P₂) (𝟙 S.obj)) at h₀
  let c := derivedBimoduleComposeResolutionValueIso A B D L hL
    ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj) S r hr P₂
  have hpost := congrArg (fun f => c.hom ≫ (bimoduleToDerived A B L).map f)
    (composeMap_id A B D L P₂ S.obj)
  have hlast := (congrArg (fun f => c.hom ≫ f)
    ((bimoduleToDerived A B L).map_id ((composeWith A B D L S.obj).obj P₂))).trans
      (Category.comp_id _)
  replace h₀ := h₀.trans (hpost.trans hlast)
  change ((derivedBimoduleComposeFunctor A B D L hL).map
      ((bimoduleToDerived A D L).map k)).app ((bimoduleToDerived A B D).obj P₂) ≫
      (derivedBimoduleComposeResolutionValueIso A B D L hL
        ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q.obj)
        S a ha P₂).hom =
    (middleRestrictionSourceComputation A B E D L F hL P₀ R.obj S r hr).hom at h₀
  have h₁ := derivedBimoduleComposeResolutionValueIso_first_naturality A B D L hL
    ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q.obj) S a ha
    (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P).hom
  change (((derivedBimoduleComposeFunctor A B D L hL).map
      ((bimoduleToDerived A D L).map k)).app ((bimoduleToDerived A B D).obj P₂) ≫
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q.obj))).map
      ((bimoduleToDerived A B D).map
        (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P).hom)) ≫
      (middleRestrictionSourceComputation A B T D L (F.comp G) hL P Q.obj S a ha).hom = _
  have hs := congrArg (fun f => ((derivedBimoduleComposeFunctor A B D L hL).map
    ((bimoduleToDerived A D L).map k)).app ((bimoduleToDerived A B D).obj P₂) ≫ f) h₁
  have ht := congrArg (fun f => f ≫ (bimoduleToDerived A B L).map
    (middleRestrictionCompSourceIso A B D E T L F G P S.obj).hom) h₀
  exact (Category.assoc _ _ _).trans
    (hs.trans ((Category.assoc _ _ _).symm.trans ht))

/-- 二つのdg関手と指定右K-flatモデルによる実際の導来比較は、合成関手の比較と可換。 -/
lemma derivedMiddleRestrictionComparison_functor_comp
    (P : BimoduleCategory A B T) (Q : RightKFlatBimoduleCategory A T L)
    (R : RightKFlatBimoduleCategory A E L) (S : RightKFlatBimoduleCategory A D L)
    (r : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
    (hr : BimoduleCategory.quasiIso A D L r) (hq : BimoduleCategory.quasiIso A E L q) :
    (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj q hq).hom ≫
        derivedMiddleRestrictionComparison A B T D L (F.comp G) hL P Q S
          (BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q)
          (BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
            A D E T L F G r q hr hq) =
      derivedMiddleRestrictionComparison A B E D L F hL
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) R S r hr ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map ((bimoduleToDerived A E L).map q)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        derivedMiddleRestrictionComparison A B T E L G hL P Q R q hq := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P
  let a := BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G r q
  have ha := BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
    A D E T L F G r q hr hq
  let c₀ := middleRestrictionSourceComputation A B E D L F hL P₀ R.obj S r hr
  let c₁ := middleRestrictionSourceComputation A B T E L G hL P Q.obj R q hq
  let c₂ := middleRestrictionSourceComputation A B T D L (F.comp G) hL P Q.obj S a ha
  let i := derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj q hq
  let τ := derivedBimoduleComposeKFlatValueIso A B E L hL R P₀
  let v := ((derivedBimoduleComposeFunctor A B E L hL).map
    ((bimoduleToDerived A E L).map q)).app ((bimoduleToDerived A B E).obj P₀)
  let f := (bimoduleToDerived A B L).map
    (middleRestrictionResolvedMap A B E D L F P₀ R.obj S.obj r)
  let g := (bimoduleToDerived A B L).map
    (middleRestrictionResolvedMap A B T E L G P Q.obj R.obj q)
  let t := (bimoduleToDerived A B L).map
    (middleRestrictionResolvedMap A B T D L (F.comp G) P Q.obj S.obj a)
  let j := (bimoduleToDerived A B L).map
    (middleRestrictionCompSourceIso A B D E T L F G P S.obj).hom
  have hi : i.hom ≫ c₂.hom = c₀.hom ≫ j :=
    derivedMiddleCompositeSourceIso_computation A B D L hL E T F G P Q R S r q hr hq
  have hv : v ≫ c₁.hom = τ.hom :=
    derivedBimoduleComposeResolutionValueIso_fac A B E L hL _ R q hq P₀
  have hj : j ≫ t = f ≫ g := by
    have h := congrArg (fun k => (bimoduleToDerived A B L).map k)
      (middleRestrictionResolvedMap_functor_comp A B D E T L F G P Q.obj R.obj S.obj r q)
    simpa only [CategoryTheory.Functor.map_comp] using h
  apply (Iso.cancel_iso_hom_right _ _ (derivedBimoduleComposeKFlatValueIso A B T L hL Q P)).1
  unfold derivedMiddleRestrictionComparison
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change i.hom ≫ c₂.hom ≫ t = c₀.hom ≫ f ≫ τ.inv ≫ v ≫ c₁.hom ≫ g
  rw [← Category.assoc i.hom c₂.hom t, hi, Category.assoc, hj,
    ← Category.assoc v c₁.hom g, hv, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
