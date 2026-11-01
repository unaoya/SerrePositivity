module
public import SerrePositivity.DifferentialGraded.Tensor.Compose
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorFunctor
public import SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionIdentification
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLiftIso

/-! # 外側右制限と固定K-flat後因子による導来合成の比較

## 概要
外側右制限と固定K-flat後因子による導来合成の比較。

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
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B)

/-- 外側右制限の交換を、閉零前因子に自然な同型へ束ねる。 -/
def composeWithRightRestrictionIso (Q : BimoduleCategory A C E) :
    BimoduleCategory.middleRightRestrictionFunctor A B D C F ⋙ composeWith A D C E Q ≅
      composeWith A B C E Q ⋙ BimoduleCategory.middleRightRestrictionFunctor A B D E F :=
  NatIso.ofComponents (fun P => composeRightRestrictionIso A B D C E F P Q) (by
    intro P P' f
    change composeMap A D C E
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map f) (𝟙 Q) ≫
        (composeRightRestrictionIso A B D C E F P' Q).hom =
      (composeRightRestrictionIso A B D C E F P Q).hom ≫
        (BimoduleCategory.middleRightRestrictionFunctor A B D E F).map
          (composeMap A B C E f (𝟙 Q))
    exact composeRightRestrictionIso_naturality A B D C E F f (𝟙 Q))

lemma composeWithRightRestrictionIso_naturality
    {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q') :
    whiskerLeft (BimoduleCategory.middleRightRestrictionFunctor A B D C F)
        (composeWithMap A D C E g) ≫ (composeWithRightRestrictionIso A B D C E F Q').hom =
      (composeWithRightRestrictionIso A B D C E F Q).hom ≫
        whiskerRight (composeWithMap A B C E g)
          (BimoduleCategory.middleRightRestrictionFunctor A B D E F) := by
  apply NatTrans.ext
  funext P
  change composeMap A D C E
        (𝟙 ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P)) g ≫
        (composeRightRestrictionIso A B D C E F P Q').hom =
      (composeRightRestrictionIso A B D C E F P Q).hom ≫
        (BimoduleCategory.middleRightRestrictionFunctor A B D E F).map
          (composeMap A B C E (𝟙 P) g)
  simpa only [CategoryTheory.Functor.map_id] using
    composeRightRestrictionIso_naturality A B D C E F (𝟙 P) g

variable [Small.{u} E]

/-- 閉零前因子上の比較を既存の出力側導来制限へ接続する。 -/
def composeWithRightRestrictionLocalizedIso (Q : BimoduleCategory A C E) :
    BimoduleCategory.middleRightRestrictionFunctor A B D C F ⋙ composeWith A D C E Q ⋙
        bimoduleToDerived A D E ≅
      composeWith A B C E Q ⋙ bimoduleToDerived A B E ⋙
        derivedBimoduleRestriction A D E B E F (DGFunctor.id E) :=
  Functor.isoWhiskerRight (composeWithRightRestrictionIso A B D C E F Q)
      (bimoduleToDerived A D E) ≪≫
    Functor.isoWhiskerLeft (composeWith A B C E Q) (middleRightRestrictionDerivedIso A B D F E)

/-- 固定K-flat後因子の比較を、前因子の局所化への前合成上に構成する。 -/
def derivedComposeWithRightRestrictionPreIso (Q : RightKFlatBimoduleCategory A C E) :
    bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A D C B C F (DGFunctor.id C) ⋙
          derivedComposeWith A D C E Q.obj Q.property) ≅
      bimoduleToDerived A B C ⋙ (derivedComposeWith A B C E Q.obj Q.property ⋙
        derivedBimoduleRestriction A D E B E F (DGFunctor.id E)) :=
  Functor.isoWhiskerRight (middleRightRestrictionDerivedIso A B D F C).symm
      (derivedComposeWith A D C E Q.obj Q.property) ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleRightRestrictionFunctor A B D C F)
      (eqToIso (derivedComposeWith_fac A D C E Q.obj Q.property)) ≪≫
    composeWithRightRestrictionLocalizedIso A B D C E F Q.obj ≪≫
    Functor.isoWhiskerRight (eqToIso (derivedComposeWith_fac A B C E Q.obj Q.property)).symm
      (derivedBimoduleRestriction A D E B E F (DGFunctor.id E))

/-- 任意の導来前因子と固定右K-flat後因子での、外側右制限と合成の比較。 -/
def derivedComposeWithRightRestrictionIso (Q : RightKFlatBimoduleCategory A C E) :
    derivedBimoduleRestriction A D C B C F (DGFunctor.id C) ⋙
        derivedComposeWith A D C E Q.obj Q.property ≅
      derivedComposeWith A B C E Q.obj Q.property ⋙
        derivedBimoduleRestriction A D E B E F (DGFunctor.id E) :=
  bimoduleDerivedIsoOfPrecomp A B C _ _
    (derivedComposeWithRightRestrictionPreIso A B D C E F Q)

lemma derivedComposeWithRightRestrictionIso_hom_app
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithRightRestrictionIso A B D C E F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWithRightRestrictionPreIso A B D C E F Q).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

end SerrePositivity.DifferentialGraded.BimoduleTensor
