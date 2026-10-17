module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFunctorComposition
public import SerrePositivity.DifferentialGraded.Bimodule.SemifreeRetarget

/-! # 標準semifree解像度による導来中間比較のdg関手合成則

## 概要
標準semifree解像度による導来中間比較のdg関手合成則。

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
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 二段階の標準解像度による比較は、合成関手へ直接適用する標準比較と可換。 -/
lemma derivedMiddleRestrictionCanonicalComparison_functor_comp
    (P : BimoduleCategory A B T) (Q : RightKFlatBimoduleCategory A T L) :
    let R := bimoduleCanonicalSemifreeResolution A E L
      ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
    (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj R.π R.quasiIso).hom ≫
        derivedMiddleRestrictionCanonicalComparison A B T D L (F.comp G) hL P Q =
      derivedMiddleRestrictionCanonicalComparison A B E D L F hL
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)
          (R.toRightKFlat A E L hL) ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map ((bimoduleToDerived A E L).map R.π)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        derivedMiddleRestrictionCanonicalComparison A B T E L G hL P Q := by
  let R := bimoduleCanonicalSemifreeResolution A E L
    ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
  let S := bimoduleCanonicalSemifreeResolution A D L
    ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R.obj)
  let k := BimoduleCategory.middleRightRestrictionCompositeMap A D E T L F G R.π
  have hk := BimoduleCategory.middleRightRestrictionCompositeMap_quasiIso
    A D E T L F G R.π R.quasiIso
  let S' := S.postcompose A D L k hk
  have hi := derivedMiddleRestrictionComparison_semifree_eq_canonical A B T D L
    (F.comp G) hL Q S' P
  change derivedMiddleRestrictionComparison A B T D L (F.comp G) hL P Q
      (S.toRightKFlat A D L hL)
      (BimoduleCategory.resolvedRestrictionAugmentationComp A D E T L F G S.π R.π)
      (BimoduleCategory.resolvedRestrictionAugmentationComp_quasiIso
        A D E T L F G S.π R.π S.quasiIso R.quasiIso) =
    derivedMiddleRestrictionCanonicalComparison A B T D L (F.comp G) hL P Q at hi
  have h := derivedMiddleRestrictionComparison_functor_comp A B D L hL E T F G P Q
    (R.toRightKFlat A E L hL) (S.toRightKFlat A D L hL) S.π R.π S.quasiIso R.quasiIso
  rw [hi] at h
  exact h

/-- 標準解像度による恒等比較も、解像度を含まない左右の恒等制限比較に一致する。 -/
lemma derivedMiddleRestrictionCanonicalComparison_functor_id
    (P : BimoduleCategory A B D) (Q : RightKFlatBimoduleCategory A D L) :
    derivedMiddleRestrictionCanonicalComparison A B D D L (DGFunctor.id D) hL P Q =
      (derivedMiddleIdentitySourceIso A B D L hL P Q.obj).hom :=
  derivedMiddleRestrictionComparison_functor_id A B D L hL P Q
    (rightKFlatResolutionObj A D L hL
      ((BimoduleCategory.middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q.obj))
    (bimoduleCanonicalSemifreeResolution A D L _).π
    (bimoduleCanonicalSemifreeResolution A D L _).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
