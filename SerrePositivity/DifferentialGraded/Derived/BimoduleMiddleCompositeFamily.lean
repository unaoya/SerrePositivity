module
public import SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionComposition
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparisonComputation

/-! # 二段階の中間dg圏制限による全導来合成比較のsource

## 概要
二段階の中間dg圏制限による全導来合成比較のsource。

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
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 二段階の比較を合成する際の、両変数の全導来圏上の実際のsource。 -/
def middleIteratedDerivedSource : DerivedBimoduleCategory A T L ⥤
    (DerivedBimoduleCategory A B T ⥤ DerivedBimoduleCategory A B L) :=
  derivedBimoduleRestriction A E L T L G (DGFunctor.id L) ⋙
    middleRestrictionDerivedSource A B E D L F hL ⋙
      (whiskeringLeft _ _ _).obj
        (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G)

/-- 左右の導来制限の合成同型だけから構成するsourceの正規化。 -/
def middleIteratedDerivedSourceIso :
    middleIteratedDerivedSource A B D E T L F G hL ≅
      middleRestrictionDerivedSource A B T D L (F.comp G) hL :=
  Functor.isoWhiskerRight (middleRightDerivedCompIso A L D E T F G)
      (derivedBimoduleComposeFunctor A B D L hL ⋙
        (whiskeringLeft _ _ _).obj
          (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G ⋙
            derivedBimoduleRestriction A B D B E (DGFunctor.id B) F)) ≪≫
    Functor.isoWhiskerLeft
      (derivedBimoduleRestriction A D L T L (F.comp G) (DGFunctor.id L) ⋙
        derivedBimoduleComposeFunctor A B D L hL)
      ((whiskeringLeft _ _ _).mapIso (middleLeftDerivedCompIso A B D E T F G))

/-- 既存の全導来中間比較を実際に二段階で適用した自然変換。 -/
def middleIteratedDerivedComparison :
    middleIteratedDerivedSource A B D E T L F G hL ⟶
      derivedBimoduleComposeFunctor A B T L hL :=
  whiskerRight
      (whiskerLeft (derivedBimoduleRestriction A E L T L G (DGFunctor.id L))
        (derivedMiddleRestrictionNatTrans A B E D L F hL))
      ((whiskeringLeft _ _ _).obj
        (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G)) ≫
    derivedMiddleRestrictionNatTrans A B T E L G hL

/-- sourceの正規化は右制限の合成比較、次に左制限の合成比較を適用する。 -/
lemma middleIteratedDerivedSourceIso_hom_app
    (Q : DerivedBimoduleCategory A T L) (P : DerivedBimoduleCategory A B T) :
    ((middleIteratedDerivedSourceIso A B D E T L F G hL).hom.app Q).app P =
      ((derivedBimoduleComposeFunctor A B D L hL).map
        ((middleRightDerivedCompIso A L D E T F G).hom.app Q)).app
          ((derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).obj
            ((derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj P)) ≫
        ((derivedBimoduleComposeFunctor A B D L hL).obj
          ((derivedBimoduleRestriction A D L T L (F.comp G) (DGFunctor.id L)).obj Q)).map
          ((middleLeftDerivedCompIso A B D E T F G).hom.app P) := rfl

/-- 二段階比較の成分は既存の実際の比較二つの合成である。 -/
lemma middleIteratedDerivedComparison_app
    (Q : DerivedBimoduleCategory A T L) (P : DerivedBimoduleCategory A B T) :
    ((middleIteratedDerivedComparison A B D E T L F G hL).app Q).app P =
      ((derivedMiddleRestrictionNatTrans A B E D L F hL).app
        ((derivedBimoduleRestriction A E L T L G (DGFunctor.id L)).obj Q)).app
          ((derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj P) ≫
        ((derivedMiddleRestrictionNatTrans A B T E L G hL).app Q).app P := rfl

include hL in
/-- 全導来関手族の等式は、右K-flat後因子と任意の閉零前因子で検査できる。 -/
lemma middleDerivedFamily_ext
    {U V : DerivedBimoduleCategory A T L ⥤
      (DerivedBimoduleCategory A B T ⥤ DerivedBimoduleCategory A B L)}
    {α β : U ⟶ V}
    (h : ∀ (Q : RightKFlatBimoduleCategory A T L) (P : BimoduleCategory A B T),
      (α.app ((bimoduleToDerived A T L).obj Q.obj)).app
          ((bimoduleToDerived A B T).obj P) =
        (β.app ((bimoduleToDerived A T L).obj Q.obj)).app
          ((bimoduleToDerived A B T).obj P)) : α = β := by
  apply bimoduleDerivedNatTrans_ext A T L
  intro Q
  let R := rightKFlatResolutionObj A T L hL Q
  let e := rightKFlatResolutionDerivedIso A T L hL Q
  apply (cancel_epi (U.map e.hom)).mp
  rw [α.naturality, β.naturality]
  have hh : α.app ((bimoduleToDerived A T L).obj R.obj) =
      β.app ((bimoduleToDerived A T L).obj R.obj) := by
    apply bimoduleDerivedNatTrans_ext A B T
    exact h R
  exact congrArg (fun f => f ≫ V.map e.hom) hh

end SerrePositivity.DifferentialGraded.BimoduleTensor
