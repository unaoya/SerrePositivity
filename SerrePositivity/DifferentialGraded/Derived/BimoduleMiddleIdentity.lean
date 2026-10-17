module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleResolvedCoherence

/-! # 恒等dg関手の実際の導来中間比較と制限の恒等自然同型の整合性

## 概要
恒等dg関手の実際の導来中間比較と制限の恒等自然同型の整合性。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (L : Type z) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

/-- K-flat後因子での計算同型は、前因子の閉零射にも自然。 -/
lemma derivedBimoduleComposeKFlatValueIso_first_naturality
    (Q : RightKFlatBimoduleCategory A D L) {P P' : BimoduleCategory A B D} (f : P ⟶ P') :
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj Q.obj)).map
        ((bimoduleToDerived A B D).map f) ≫
      (derivedBimoduleComposeKFlatValueIso A B D L hL Q P').hom =
    (derivedBimoduleComposeKFlatValueIso A B D L hL Q P).hom ≫
      (bimoduleToDerived A B L).map (composeMap A B D L f (𝟙 Q.obj)) :=
  (derivedBimoduleComposeKFlatIso A B D L hL Q).hom.naturality
    ((bimoduleToDerived A B D).map f)

lemma derivedBimoduleComposeResolutionValueIso_self
    (Q : RightKFlatBimoduleCategory A D L) (P : BimoduleCategory A B D) :
    derivedBimoduleComposeResolutionValueIso A B D L hL Q.obj Q (𝟙 Q.obj)
        ((BimoduleCategory.quasiIso A D L).id_mem Q.obj) P =
      derivedBimoduleComposeKFlatValueIso A B D L hL Q P := by
  unfold derivedBimoduleComposeResolutionValueIso
  rw [derivedBimoduleComposeResolutionComputation_self]
  apply Iso.ext
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- 恒等の左右制限比較を既存の全導来合成へ送った、選択された解像度に依存しないsource同型。 -/
def derivedMiddleIdentitySourceIso (P : BimoduleCategory A B D)
    (Q : BimoduleCategory A D L) :
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P)) ≅
      ((derivedBimoduleComposeFunctor A B D L hL).obj
        ((bimoduleToDerived A D L).obj Q)).obj ((bimoduleToDerived A B D).obj P) :=
  ((derivedBimoduleComposeFunctor A B D L hL).mapIso
      ((bimoduleToDerived A D L).mapIso
        (BimoduleCategory.middleRightRestrictionIdObjIso A D L Q))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P)) ≪≫
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj Q)).mapIso
      ((bimoduleToDerived A B D).mapIso (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P))

/-- 恒等dg関手の実際の導来比較は、左右の恒等制限比較から作るsource同型そのもの。 -/
lemma derivedMiddleRestrictionComparison_functor_id
    (P : BimoduleCategory A B D) (Q R : RightKFlatBimoduleCategory A D L)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj
      Q.obj) (hq : BimoduleCategory.quasiIso A D L q) :
    derivedMiddleRestrictionComparison A B D D L (DGFunctor.id D) hL P Q R q hq =
      (derivedMiddleIdentitySourceIso A B D L hL P Q.obj).hom := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P
  let a := BimoduleCategory.resolvedRestrictionAugmentationId A D L q
  let r : R ⟶ Q := ⟨a⟩
  let f := (BimoduleCategory.middleRightRestrictionIdObjIso A D L Q.obj).hom
  let g := (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P).hom
  have hn := derivedBimoduleComposeResolutionValueIso_naturality A B D L hL R Q q
    (𝟙 Q.obj) hq ((BimoduleCategory.quasiIso A D L).id_mem Q.obj) f r (by
      change (bimoduleToDerived A D L).map q ≫ (bimoduleToDerived A D L).map f =
        (bimoduleToDerived A D L).map a ≫ (bimoduleToDerived A D L).map (𝟙 Q.obj)
      rw [CategoryTheory.Functor.map_id, Category.comp_id, ← CategoryTheory.Functor.map_comp]
      rfl) P₀
  rw [derivedBimoduleComposeResolutionValueIso_self] at hn
  change ((derivedBimoduleComposeFunctor A B D L hL).map
      ((bimoduleToDerived A D L).map f)).app ((bimoduleToDerived A B D).obj P₀) ≫
      (derivedBimoduleComposeKFlatValueIso A B D L hL Q P₀).hom =
    (middleRestrictionSourceComputation A B D D L (DGFunctor.id D) hL P Q.obj R q hq).hom ≫
      (bimoduleToDerived A B L).map (composeMap A B D L (𝟙 P₀) a) at hn
  have ht := derivedBimoduleComposeKFlatValueIso_first_naturality A B D L hL Q g
  have hr := congrArg (fun k => (bimoduleToDerived A B L).map k)
    (middleRestrictionResolvedMap_functor_id_exchange A B D L P Q.obj R.obj q)
  rw [CategoryTheory.Functor.map_comp] at hr
  apply (Iso.cancel_iso_hom_right _ _ (derivedBimoduleComposeKFlatValueIso A B D L hL Q P)).1
  unfold derivedMiddleRestrictionComparison
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (middleRestrictionSourceComputation A B D D L (DGFunctor.id D) hL P Q.obj R q hq).hom ≫
      (bimoduleToDerived A B L).map
        (middleRestrictionResolvedMap A B D D L (DGFunctor.id D) P Q.obj R.obj q) =
    (((derivedBimoduleComposeFunctor A B D L hL).map
      ((bimoduleToDerived A D L).map f)).app ((bimoduleToDerived A B D).obj P₀) ≫
      ((derivedBimoduleComposeFunctor A B D L hL).obj
        ((bimoduleToDerived A D L).obj Q.obj)).map ((bimoduleToDerived A B D).map g)) ≫
      (derivedBimoduleComposeKFlatValueIso A B D L hL Q P).hom
  rw [hr, ← Category.assoc, ← hn, Category.assoc, ← ht, ← Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
