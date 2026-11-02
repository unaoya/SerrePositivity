module

public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Tensor.Compose
public import SerrePositivity.DifferentialGraded.Derived.KFlat
public import SerrePositivity.DifferentialGraded.Derived.Functor
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensor
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.ModelIndependence
public import Mathlib.CategoryTheory.Whiskering

/-!
# Derived.Bimodule

## 概要
14 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## MiddleRestrictionIdentification（旧 SerrePositivity/DifferentialGraded/Derived/MiddleRestrictionIdentification.lean） -/

/-! # 直接の中間制限と既存の積dg圏表示によるbimodule制限の同定

## 概要
直接の中間制限と既存の積dg圏表示によるbimodule制限の同定。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleRestrictionIdentification
universe u v w z t

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory BimoduleTensorModule
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)

/-- 直接の左制限は既存の積dg圏表示による制限と自然同型。 -/
def middleLeftRestrictionIso :
    BimoduleCategory.middleLeftRestrictionFunctor A B C D F ≅
      bimoduleRestriction A B D B C (DGFunctor.id B) F :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C D F)
      (rightModuleCounitIso A B D).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (middleLeftPresentationIso A B C D F)
      (rightModuleBimoduleEquivalence A B D).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (rightModuleInverseIso A B C)
      (moduleRestriction A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        ((DGFunctor.id Bᵒᵖ).tensor F).op.op ⋙ (rightModuleBimoduleEquivalence A B D).functor)

variable (E : Type t) [DGCategory A E] [Small.{u} E]

/-- 直接の右制限は既存の積dg圏表示による制限と自然同型。 -/
def middleRightRestrictionIso :
    BimoduleCategory.middleRightRestrictionFunctor A C D E F ≅
      bimoduleRestriction A D E C E F (DGFunctor.id E) :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleRightRestrictionFunctor A C D E F)
      (rightModuleCounitIso A D E).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (middleRightPresentationIso A C D F E)
      (rightModuleBimoduleEquivalence A D E).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (rightModuleInverseIso A C E)
      (moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (DGTensorCategory A Cᵒᵖ E)ᵒᵖ
        (F.op.tensor (DGFunctor.id E)).op.op ⋙ (rightModuleBimoduleEquivalence A D E).functor)

/-- 左制限の局所化は既存の導来制限と自然に可換する。 -/
def middleLeftRestrictionDerivedIso :
    BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ bimoduleToDerived A B D ≅
      bimoduleToDerived A B C ⋙
        derivedBimoduleRestriction A B D B C (DGFunctor.id B) F :=
  Functor.isoWhiskerRight (middleLeftRestrictionIso A B C D F) (bimoduleToDerived A B D) ≪≫
    (eqToIso (derivedBimoduleRestriction_fac A B D B C (DGFunctor.id B) F)).symm

/-- 右制限の局所化も既存の導来制限と自然に可換する。 -/
def middleRightRestrictionDerivedIso :
    BimoduleCategory.middleRightRestrictionFunctor A C D E F ⋙ bimoduleToDerived A D E ≅
      bimoduleToDerived A C E ⋙
        derivedBimoduleRestriction A D E C E F (DGFunctor.id E) :=
  Functor.isoWhiskerRight (middleRightRestrictionIso A C D F E) (bimoduleToDerived A D E) ≪≫
    (eqToIso (derivedBimoduleRestriction_fac A D E C E F (DGFunctor.id E))).symm

end SerrePositivity.DifferentialGraded
end

end MiddleRestrictionIdentification

/-! ## MiddleRestrictionComposition（旧 SerrePositivity/DifferentialGraded/Derived/MiddleRestrictionComposition.lean） -/

/-! # 既存の導来bimodule制限の二段階合成の正規化

## 概要
既存の導来bimodule制限の二段階合成の正規化。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleRestrictionComposition
universe u v w z t

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 元の対象に前合成した導来左制限の合成比較。直接制限の合成同型から構成する。 -/
def middleLeftDerivedCompPreIso :
    bimoduleToDerived A B T ⋙
        (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G ⋙
          derivedBimoduleRestriction A B D B E (DGFunctor.id B) F) ≅
      bimoduleToDerived A B T ⋙
        derivedBimoduleRestriction A B D B T (DGFunctor.id B) (F.comp G) :=
  Functor.isoWhiskerRight (middleLeftRestrictionDerivedIso A B T E G).symm
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F) ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B T E G)
      (middleLeftRestrictionDerivedIso A B E D F).symm ≪≫
    Functor.isoWhiskerRight (BimoduleCategory.middleLeftRestrictionCompIso A B D E T F G)
      (bimoduleToDerived A B D) ≪≫
    middleLeftRestrictionDerivedIso A B T D (F.comp G)

/-- 左制限の合成比較を全導来圏上の自然同型へ降ろす。 -/
def middleLeftDerivedCompIso :
    derivedBimoduleRestriction A B E B T (DGFunctor.id B) G ⋙
        derivedBimoduleRestriction A B D B E (DGFunctor.id B) F ≅
      derivedBimoduleRestriction A B D B T (DGFunctor.id B) (F.comp G) :=
  bimoduleDerivedIsoOfPrecomp A B T _ _ (middleLeftDerivedCompPreIso A B D E T F G)

lemma middleLeftDerivedCompIso_hom_app (P : BimoduleCategory A B T) :
    (middleLeftDerivedCompIso A B D E T F G).hom.app ((bimoduleToDerived A B T).obj P) =
      (middleLeftDerivedCompPreIso A B D E T F G).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B T _ _ _ P

/-- 元の対象に前合成した導来右制限の合成比較。 -/
def middleRightDerivedCompPreIso :
    bimoduleToDerived A T B ⋙
        (derivedBimoduleRestriction A E B T B G (DGFunctor.id B) ⋙
          derivedBimoduleRestriction A D B E B F (DGFunctor.id B)) ≅
      bimoduleToDerived A T B ⋙
        derivedBimoduleRestriction A D B T B (F.comp G) (DGFunctor.id B) :=
  Functor.isoWhiskerRight (middleRightRestrictionDerivedIso A T E G B).symm
      (derivedBimoduleRestriction A D B E B F (DGFunctor.id B)) ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleRightRestrictionFunctor A T E B G)
      (middleRightRestrictionDerivedIso A E D F B).symm ≪≫
    Functor.isoWhiskerRight (BimoduleCategory.middleRightRestrictionCompIso A D B E T F G)
      (bimoduleToDerived A D B) ≪≫
    middleRightRestrictionDerivedIso A T D (F.comp G) B

/-- 右制限の合成比較を全導来圏上の自然同型へ降ろす。 -/
def middleRightDerivedCompIso :
    derivedBimoduleRestriction A E B T B G (DGFunctor.id B) ⋙
        derivedBimoduleRestriction A D B E B F (DGFunctor.id B) ≅
      derivedBimoduleRestriction A D B T B (F.comp G) (DGFunctor.id B) :=
  bimoduleDerivedIsoOfPrecomp A T B _ _ (middleRightDerivedCompPreIso A B D E T F G)

lemma middleRightDerivedCompIso_hom_app (Q : BimoduleCategory A T B) :
    (middleRightDerivedCompIso A B D E T F G).hom.app ((bimoduleToDerived A T B).obj Q) =
      (middleRightDerivedCompPreIso A B D E T F G).hom.app Q :=
  bimoduleDerivedIsoOfPrecomp_hom_app A T B _ _ _ Q

/-- 左制限の合成比較は、直接制限との表示同型に関して可換である。 -/
lemma middleLeftDerivedCompIso_presentation (P : BimoduleCategory A B T) :
    (middleLeftRestrictionDerivedIso A B E D F).hom.app
        ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) ≫
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map
        ((middleLeftRestrictionDerivedIso A B T E G).hom.app P) ≫
      (middleLeftDerivedCompIso A B D E T F G).hom.app
        ((bimoduleToDerived A B T).obj P) =
    (bimoduleToDerived A B D).map
        (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P).hom ≫
      (middleLeftRestrictionDerivedIso A B T D (F.comp G)).hom.app P := by
  rw [middleLeftDerivedCompIso_hom_app]
  simp only [middleLeftDerivedCompPreIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    whiskerLeft_app, whiskerRight_app]
  rw [← (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp, Iso.hom_inv_id_app_assoc]
  rfl

/-- 右制限の合成比較も、直接制限との表示同型に関して可換である。 -/
lemma middleRightDerivedCompIso_presentation (Q : BimoduleCategory A T B) :
    (middleRightRestrictionDerivedIso A E D F B).hom.app
        ((BimoduleCategory.middleRightRestrictionFunctor A T E B G).obj Q) ≫
      (derivedBimoduleRestriction A D B E B F (DGFunctor.id B)).map
        ((middleRightRestrictionDerivedIso A T E G B).hom.app Q) ≫
      (middleRightDerivedCompIso A B D E T F G).hom.app
        ((bimoduleToDerived A T B).obj Q) =
    (bimoduleToDerived A D B).map
        (BimoduleCategory.middleRightRestrictionCompObjIso A D B E T F G Q).hom ≫
      (middleRightRestrictionDerivedIso A T D (F.comp G) B).hom.app Q := by
  rw [middleRightDerivedCompIso_hom_app]
  simp only [middleRightDerivedCompPreIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    whiskerLeft_app, whiskerRight_app]
  rw [← (derivedBimoduleRestriction A D B E B F (DGFunctor.id B)).map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp, Iso.hom_inv_id_app_assoc]
  rfl

/-- 元の対象への前合成では、導来合成同型は構成に使った比較を回復する。 -/
lemma middleLeftDerivedCompIso_precomp :
    whiskerLeft (bimoduleToDerived A B T) (middleLeftDerivedCompIso A B D E T F G).hom =
      (middleLeftDerivedCompPreIso A B D E T F G).hom := by
  apply NatTrans.ext
  funext P
  exact middleLeftDerivedCompIso_hom_app A B D E T F G P

lemma middleRightDerivedCompIso_precomp :
    whiskerLeft (bimoduleToDerived A T B) (middleRightDerivedCompIso A B D E T F G).hom =
      (middleRightDerivedCompPreIso A B D E T F G).hom := by
  apply NatTrans.ext
  funext Q
  exact middleRightDerivedCompIso_hom_app A B D E T F G Q

end SerrePositivity.DifferentialGraded
end

end MiddleRestrictionComposition

/-! ## MiddleRestrictionIteratedPresentation（旧 SerrePositivity/DifferentialGraded/Derived/MiddleRestrictionIteratedPresentation.lean） -/

/-! # 二段階の直接制限から既存の導来制限への表示同型

## 概要
二段階の直接制限から既存の導来制限への表示同型。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleRestrictionIteratedPresentation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階の直接左制限の局所化を、既存の二段階導来制限へ送る。 -/
def middleLeftIteratedDerivedIso :
    BimoduleCategory.middleLeftRestrictionFunctor A B T E G ⋙
        BimoduleCategory.middleLeftRestrictionFunctor A B E D F ⋙ bimoduleToDerived A B D ≅
      bimoduleToDerived A B T ⋙
        derivedBimoduleRestriction A B E B T (DGFunctor.id B) G ⋙
          derivedBimoduleRestriction A B D B E (DGFunctor.id B) F :=
  Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B T E G)
      (middleLeftRestrictionDerivedIso A B E D F) ≪≫
    Functor.isoWhiskerRight (middleLeftRestrictionDerivedIso A B T E G)
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F)

lemma middleLeftIteratedDerivedIso_normalize :
    (middleLeftIteratedDerivedIso A B D E T F G).hom ≫
        whiskerLeft (bimoduleToDerived A B T) (middleLeftDerivedCompIso A B D E T F G).hom =
      whiskerRight (BimoduleCategory.middleLeftRestrictionCompIso A B D E T F G).hom
          (bimoduleToDerived A B D) ≫
        (middleLeftRestrictionDerivedIso A B T D (F.comp G)).hom := by
  apply NatTrans.ext
  funext P
  simpa only [middleLeftIteratedDerivedIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, BimoduleCategory.middleLeftRestrictionCompIso, NatIso.ofComponents_hom_app,
    Category.assoc] using
    middleLeftDerivedCompIso_presentation A B D E T F G P

/-- 二段階の直接右制限の局所化を、既存の二段階導来制限へ送る。 -/
def middleRightIteratedDerivedIso :
    BimoduleCategory.middleRightRestrictionFunctor A T E B G ⋙
        BimoduleCategory.middleRightRestrictionFunctor A E D B F ⋙ bimoduleToDerived A D B ≅
      bimoduleToDerived A T B ⋙
        derivedBimoduleRestriction A E B T B G (DGFunctor.id B) ⋙
          derivedBimoduleRestriction A D B E B F (DGFunctor.id B) :=
  Functor.isoWhiskerLeft (BimoduleCategory.middleRightRestrictionFunctor A T E B G)
      (middleRightRestrictionDerivedIso A E D F B) ≪≫
    Functor.isoWhiskerRight (middleRightRestrictionDerivedIso A T E G B)
      (derivedBimoduleRestriction A D B E B F (DGFunctor.id B))

lemma middleRightIteratedDerivedIso_normalize :
    (middleRightIteratedDerivedIso A B D E T F G).hom ≫
        whiskerLeft (bimoduleToDerived A T B) (middleRightDerivedCompIso A B D E T F G).hom =
      whiskerRight (BimoduleCategory.middleRightRestrictionCompIso A D B E T F G).hom
          (bimoduleToDerived A D B) ≫
        (middleRightRestrictionDerivedIso A T D (F.comp G) B).hom := by
  apply NatTrans.ext
  funext Q
  simpa only [middleRightIteratedDerivedIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, BimoduleCategory.middleRightRestrictionCompIso, NatIso.ofComponents_hom_app,
    Category.assoc] using
    middleRightDerivedCompIso_presentation A B D E T F G Q

end SerrePositivity.DifferentialGraded
end

end MiddleRestrictionIteratedPresentation

/-! ## BimoduleLeftRestrictionBase（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleLeftRestrictionBase.lean） -/

/-! # 外側左制限と固定K-flat後因子による導来合成の比較

## 概要
外側左制限と固定K-flat後因子による導来合成の比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleLeftRestrictionBase
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] (D : Type t) [DGCategory A D] (F : DGFunctor A D E)

/-- 外側左制限の交換を、任意の閉零前因子に自然な同型に束ねる。 -/
def composeWithLeftRestrictionIso (Q : BimoduleCategory A C E) :
    composeWith A B C D ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).obj Q) ≅
      composeWith A B C E Q ⋙ BimoduleCategory.middleLeftRestrictionFunctor A B E D F :=
  NatIso.ofComponents (fun P => composeLeftRestrictionIso A B C E D F P Q) (by
    intro P P' f
    change composeMap A B C D f
        (𝟙 ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).obj Q)) ≫
        (composeLeftRestrictionIso A B C E D F P' Q).hom =
      (composeLeftRestrictionIso A B C E D F P Q).hom ≫
        (BimoduleCategory.middleLeftRestrictionFunctor A B E D F).map
          (composeMap A B C E f (𝟙 Q))
    have h := composeLeftRestrictionIso_naturality A B C E D F f (𝟙 Q)
    simpa only [CategoryTheory.Functor.map_id] using h)

/-- 外側左制限の交換同型は、後因子の任意の閉零射にも自然。 -/
lemma composeWithLeftRestrictionIso_naturality
    {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q') :
    composeWithMap A B C D ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map g) ≫
        (composeWithLeftRestrictionIso A B C E D F Q').hom =
      (composeWithLeftRestrictionIso A B C E D F Q).hom ≫
        whiskerRight (composeWithMap A B C E g)
          (BimoduleCategory.middleLeftRestrictionFunctor A B E D F) := by
  apply NatTrans.ext
  funext P
  change composeMap A B C D (𝟙 P)
        ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map g) ≫
        (composeLeftRestrictionIso A B C E D F P Q').hom =
      (composeLeftRestrictionIso A B C E D F P Q).hom ≫
        (BimoduleCategory.middleLeftRestrictionFunctor A B E D F).map
          (composeMap A B C E (𝟙 P) g)
  exact composeLeftRestrictionIso_naturality A B C E D F (𝟙 P) g

variable [Small.{u} E] [Small.{u} D]

/-- 閉零前因子上の比較を、既存の出力側導来制限へ接続する。 -/
def composeWithLeftRestrictionLocalizedIso (Q : BimoduleCategory A C E) :
    composeWith A B C D ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).obj Q) ⋙
        bimoduleToDerived A B D ≅
      composeWith A B C E Q ⋙ bimoduleToDerived A B E ⋙
        derivedBimoduleRestriction A B D B E (DGFunctor.id B) F :=
  Functor.isoWhiskerRight (composeWithLeftRestrictionIso A B C E D F Q)
      (bimoduleToDerived A B D) ≪≫
    Functor.isoWhiskerLeft (composeWith A B C E Q) (middleLeftRestrictionDerivedIso A B E D F)

/-- 固定右K-flat後因子について、局所化前に構成する前合成比較。 -/
def derivedComposeWithLeftRestrictionPreIso (Q : RightKFlatBimoduleCategory A C E) :
    bimoduleToDerived A B C ⋙
        derivedComposeWith A B C D ((rightKFlatLeftRestriction A C E D F).obj Q).obj
          ((rightKFlatLeftRestriction A C E D F).obj Q).property ≅
      bimoduleToDerived A B C ⋙ (derivedComposeWith A B C E Q.obj Q.property ⋙
        derivedBimoduleRestriction A B D B E (DGFunctor.id B) F) :=
  eqToIso (derivedComposeWith_fac A B C D _
      ((rightKFlatLeftRestriction A C E D F).obj Q).property) ≪≫
    composeWithLeftRestrictionLocalizedIso A B C E D F Q.obj ≪≫
    Functor.isoWhiskerRight (eqToIso (derivedComposeWith_fac A B C E Q.obj Q.property)).symm
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F)

/-- 前因子は全導来圏、後因子は任意の指定右K-flatモデルにおける外側左制限の比較。 -/
def derivedComposeWithLeftRestrictionIso (Q : RightKFlatBimoduleCategory A C E) :
    derivedComposeWith A B C D ((rightKFlatLeftRestriction A C E D F).obj Q).obj
        ((rightKFlatLeftRestriction A C E D F).obj Q).property ≅
      derivedComposeWith A B C E Q.obj Q.property ⋙
        derivedBimoduleRestriction A B D B E (DGFunctor.id B) F :=
  bimoduleDerivedIsoOfPrecomp A B C _ _
    (derivedComposeWithLeftRestrictionPreIso A B C E D F Q)

lemma derivedComposeWithLeftRestrictionIso_hom_app
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWithLeftRestrictionPreIso A B C E D F Q).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleLeftRestrictionBase

/-! ## BimoduleLeftRestrictionFamily（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleLeftRestrictionFamily.lean） -/

/-! # 外側左制限の導来合成比較を右K-flat後因子の関手族へ束ねる

## 概要
外側左制限の導来合成比較を右K-flat後因子の関手族へ束ねる。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleLeftRestrictionFamily
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)

/-- 元の前因子上で、固定K-flat後因子の比較を既存の計算同型で表示する。 -/
lemma derivedComposeWithLeftRestrictionIso_hom_app_calc
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWithComputation A B C D
          ((rightKFlatLeftRestriction A C E D F).obj Q).obj
          ((rightKFlatLeftRestriction A C E D F).obj Q).property P).hom ≫
        (bimoduleToDerived A B D).map (composeLeftRestrictionIso A B C E D F P Q.obj).hom ≫
        (middleLeftRestrictionDerivedIso A B E D F).hom.app
          ((composeWith A B C E Q.obj).obj P) ≫
        (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map
          (derivedComposeWithComputation A B C E Q.obj Q.property P).inv := by
  rw [derivedComposeWithLeftRestrictionIso_hom_app]
  simp only [derivedComposeWithLeftRestrictionPreIso, composeWithLeftRestrictionLocalizedIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Category.assoc]
  rfl

/-- 先に外側左制限してから固定因子の導来合成を行う関手族。 -/
def leftRestrictionKFlatComposeSource : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B D) :=
  rightKFlatLeftRestriction A C E D F ⋙ derivedComposeWithFunctor A B C D

/-- 固定因子の導来合成を行い、その出力の外側左作用を制限する関手族。 -/
def leftRestrictionKFlatComposeTarget : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B D) :=
  derivedComposeWithFunctor A B C E ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F)

/-- 右K-flat後因子の任意の射に関する、実際の導来合成比較の自然性。 -/
lemma derivedComposeWithLeftRestrictionIso_naturality
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    (leftRestrictionKFlatComposeSource A B C E D F).map g ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q').hom =
      (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom ≫
        (leftRestrictionKFlatComposeTarget A B C E D F).map g := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  change (derivedComposeWithMap A B C D
      ((rightKFlatLeftRestriction A C E D F).obj Q).property
      ((rightKFlatLeftRestriction A C E D F).obj Q').property
      ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map g.hom)).app
        ((bimoduleToDerived A B C).obj P) ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q').hom.app
          ((bimoduleToDerived A B C).obj P) =
    (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map
        ((derivedComposeWithMap A B C E Q.property Q'.property g.hom).app
          ((bimoduleToDerived A B C).obj P))
  simp only [derivedComposeWithMap_app, derivedComposeWithLeftRestrictionIso_hom_app_calc,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have h₀ := congrArg ((bimoduleToDerived A B D).map)
    (composeLeftRestrictionIso_naturality A B C E D F (𝟙 P) g.hom)
  simp only [CategoryTheory.Functor.map_comp] at h₀
  have h₁ := (middleLeftRestrictionDerivedIso A B E D F).hom.naturality
    (composeMap A B C E (𝟙 P) g.hom)
  simp only [Functor.comp_map] at h₁
  have hn := (congrArg (fun k => k ≫
      (middleLeftRestrictionDerivedIso A B E D F).hom.app
        ((composeWith A B C E Q'.obj).obj P)) h₀).trans (by
    simpa only [Category.assoc, composeWith, composeFunctor, Functor.comp_obj,
      Functor.prod', Functor.const, Functor.id_obj] using congrArg (fun k =>
      (bimoduleToDerived A B D).map (composeLeftRestrictionIso A B C E D F P Q.obj).hom ≫ k) h₁)
  simpa only [Category.assoc, composeWith, composeFunctor, Functor.comp_obj,
      Functor.prod', Functor.const, Functor.id_obj] using congrArg (fun k =>
    (derivedComposeWithComputation A B C D
        ((rightKFlatLeftRestriction A C E D F).obj Q).obj
        ((rightKFlatLeftRestriction A C E D F).obj Q).property P).hom ≫ k ≫
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map
        (derivedComposeWithComputation A B C E Q'.obj Q'.property P).inv) hn

/-- 外側左制限の比較を、右K-flat後因子にも自然な自然同型へ束ねる。 -/
def leftRestrictionKFlatComposeIso :
    leftRestrictionKFlatComposeSource A B C E D F ≅ leftRestrictionKFlatComposeTarget A B C E D F :=
  NatIso.ofComponents (derivedComposeWithLeftRestrictionIso A B C E D F) (by
    intro Q Q' g
    exact derivedComposeWithLeftRestrictionIso_naturality A B C E D F g)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleLeftRestrictionFamily

/-! ## BimoduleLeftRestrictionFull（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleLeftRestrictionFull.lean） -/

/-! # 外側の左dg作用の制限と両変数の全導来合成の自然同型

## 概要
外側の左dg作用の制限と両変数の全導来合成の自然同型。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleLeftRestrictionFull
universe u v w z t

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D)

/-- 合成後に出力の外側左作用を制限する、既存の全導来関手族。 -/
def leftRestrictionDerivedComposeSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B D) :=
  derivedBimoduleComposeFunctor A B C E hE ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F)

/-- 後因子の外側左作用を制限してから合成する、既存の全導来関手族。 -/
def leftRestrictionDerivedComposeTarget : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B D) :=
  derivedBimoduleRestriction A C D C E (DGFunctor.id C) F ⋙
    derivedBimoduleComposeFunctor A B C D hD

/-- sourceは右K-flatモデル上で既存の固定因子関手族になる。 -/
def leftRestrictionDerivedComposeSourceBaseIso :
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        leftRestrictionDerivedComposeSource A B C E D F hE ≅
      leftRestrictionKFlatComposeTarget A B C E D F :=
  Functor.isoWhiskerRight (rightKFlatComposePresentationIso A C E hE B)
    ((whiskeringRight _ _ _).obj (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F))

/-- targetは右K-flat性を保つ直接制限による固定因子関手族になる。 -/
def leftRestrictionDerivedComposeTargetBaseIso :
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        leftRestrictionDerivedComposeTarget A B C E D F hD ≅
      leftRestrictionKFlatComposeSource A B C E D F :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (rightKFlatInclusion A C E)
        (middleLeftRestrictionDerivedIso A C E D F).symm)
      (derivedBimoduleComposeFunctor A B C D hD) ≪≫
    Functor.isoWhiskerLeft (rightKFlatLeftRestriction A C E D F)
      (rightKFlatComposePresentationIso A C D hD B)

/-- 外側の左dg作用の制限は、両変数の全導来合成と自然に可換する。 -/
def derivedBimoduleComposeLeftRestrictionIso :
    leftRestrictionDerivedComposeSource A B C E D F hE ≅
      leftRestrictionDerivedComposeTarget A B C E D F hD :=
  rightKFlatDerivedIsoOfPrecomp A C E hE _ _
    (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE ≪≫
      (leftRestrictionKFlatComposeIso A B C E D F).symm ≪≫
        (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleLeftRestrictionFull

/-! ## BimoduleLeftRestrictionComputation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleLeftRestrictionComputation.lean） -/

/-! # 全導来外側左制限比較の指定K-flatモデルによる計算

## 概要
全導来外側左制限比較の指定K-flatモデルによる計算。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleLeftRestrictionComputation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D)

/-- 指定右K-flatモデルへの前合成で、全導来比較の元の表示同型を回復する。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_precomp :
    Functor.isoWhiskerLeft (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E)
        (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD) =
      leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE ≪≫
        (leftRestrictionKFlatComposeIso A B C E D F).symm ≪≫
          (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).symm :=
  rightKFlatDerivedIsoOfPrecomp_precomp A C E hE _ _ _

/-- 右K-flatモデル上の全導来比較は、両側の表示同型と固定モデル比較の逆の合成。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_app_rightKFlat
    (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) =
      (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv ≫
          (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).inv.app Q := by
  unfold derivedBimoduleComposeLeftRestrictionIso
  rw [rightKFlatDerivedIsoOfPrecomp_hom_app]
  rfl

/-- 両側の表示を固定すると、元の固定K-flatモデルの比較を厳密に回復するsquare。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_model_square
    (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) ≫
        (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q =
      (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv := by
  rw [derivedBimoduleComposeLeftRestrictionIso_app_rightKFlat]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (fun k =>
    (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q ≫ k)
    (Category.comp_id (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv)

/-- モデル計算squareは前因子が任意の導来対象の場合にも成り立つ。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_model_square_app
    (Q : RightKFlatBimoduleCategory A C E) (P : DerivedBimoduleCategory A B C) :
    ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).hom.app
        ((bimoduleToDerived A C E).obj Q.obj)).app P ≫
        ((leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q).app P =
      ((leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q).app P ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv.app P := by
  exact NatTrans.congr_app
    (derivedBimoduleComposeLeftRestrictionIso_model_square A B C E D F hE hD Q) P

/-- 固定K-flatモデル上のsquareが同じなら、全導来比較の自然変換は一意。 -/
lemma derivedBimoduleComposeLeftRestriction_hom_unique
    {α : leftRestrictionDerivedComposeSource A B C E D F hE ⟶
      leftRestrictionDerivedComposeTarget A B C E D F hD}
    (h : ∀ Q : RightKFlatBimoduleCategory A C E,
      α.app ((bimoduleToDerived A C E).obj Q.obj) ≫
          (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q =
        (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q ≫
          (derivedComposeWithLeftRestrictionIso A B C E D F Q).inv) :
    α = (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).hom := by
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  apply (cancel_mono
    ((leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q)).mp
  exact (h Q).trans
    (derivedBimoduleComposeLeftRestrictionIso_model_square A B C E D F hE hD Q).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleLeftRestrictionComputation

/-! ## BimoduleRightRestrictionBase（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRightRestrictionBase.lean） -/

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
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleRightRestrictionBase
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end BimoduleRightRestrictionBase

/-! ## BimoduleRightRestrictionFamily（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRightRestrictionFamily.lean） -/

/-! # 外側右制限の固定K-flat合成比較の後因子自然性

## 概要
外側右制限の固定K-flat合成比較の後因子自然性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleRightRestrictionFamily
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D B)

lemma derivedComposeWithRightRestrictionIso_hom_app_calc
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithRightRestrictionIso A B D C E F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWith A D C E Q.obj Q.property).map
          ((middleRightRestrictionDerivedIso A B D F C).inv.app P) ≫
        (derivedComposeWithComputation A D C E Q.obj Q.property
          ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P)).hom ≫
        (bimoduleToDerived A D E).map (composeRightRestrictionIso A B D C E F P Q.obj).hom ≫
        (middleRightRestrictionDerivedIso A B D F E).hom.app
          ((composeWith A B C E Q.obj).obj P) ≫
        (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).map
          (derivedComposeWithComputation A B C E Q.obj Q.property P).inv := by
  rw [derivedComposeWithRightRestrictionIso_hom_app]
  simp only [derivedComposeWithRightRestrictionPreIso, composeWithRightRestrictionLocalizedIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Category.assoc]
  rfl

/-- 前因子を既存の導来制限で送ってから合成する固定後因子関手族。 -/
def rightRestrictionKFlatComposeSource : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D E) :=
  derivedComposeWithFunctor A D C E ⋙
    (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))

/-- 合成の出力を既存の導来制限で送る固定後因子関手族。 -/
def rightRestrictionKFlatComposeTarget : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D E) :=
  derivedComposeWithFunctor A B C E ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A D E B E F (DGFunctor.id E))

lemma derivedComposeWithRightRestrictionIso_naturality
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    (rightRestrictionKFlatComposeSource A B D C E F).map g ≫
        (derivedComposeWithRightRestrictionIso A B D C E F Q').hom =
      (derivedComposeWithRightRestrictionIso A B D C E F Q).hom ≫
        (rightRestrictionKFlatComposeTarget A B D C E F).map g := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  change (derivedComposeWithMap A D C E Q.property Q'.property g.hom).app
        ((derivedBimoduleRestriction A D C B C F (DGFunctor.id C)).obj
          ((bimoduleToDerived A B C).obj P)) ≫
        (derivedComposeWithRightRestrictionIso A B D C E F Q').hom.app
          ((bimoduleToDerived A B C).obj P) =
    (derivedComposeWithRightRestrictionIso A B D C E F Q).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).map
        ((derivedComposeWithMap A B C E Q.property Q'.property g.hom).app
          ((bimoduleToDerived A B C).obj P))
  rw [derivedComposeWithRightRestrictionIso_hom_app_calc,
    derivedComposeWithRightRestrictionIso_hom_app_calc]
  have hn := (derivedComposeWithMap A D C E Q.property Q'.property g.hom).naturality
    ((middleRightRestrictionDerivedIso A B D F C).inv.app P)
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  simp only [derivedComposeWithMap_app, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have h₀ := congrArg ((bimoduleToDerived A D E).map)
    (composeRightRestrictionIso_naturality A B D C E F (𝟙 P) g.hom)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h₀
  have h₁ := (middleRightRestrictionDerivedIso A B D F E).hom.naturality
    (composeMap A B C E (𝟙 P) g.hom)
  simp only [Functor.comp_map] at h₁
  have hh := (congrArg (fun k => k ≫
      (middleRightRestrictionDerivedIso A B D F E).hom.app
        ((composeWith A B C E Q'.obj).obj P)) h₀).trans (by
    simpa only [Category.assoc, composeWith, composeFunctor, Functor.comp_obj,
      Functor.prod', Functor.const, Functor.id_obj] using congrArg (fun k =>
      (bimoduleToDerived A D E).map (composeRightRestrictionIso A B D C E F P Q.obj).hom ≫ k) h₁)
  simpa only [Category.assoc, composeWith, composeFunctor, Functor.comp_obj,
    Functor.prod', Functor.const, Functor.id_obj] using congrArg (fun k =>
    (derivedComposeWith A D C E Q.obj Q.property).map
        ((middleRightRestrictionDerivedIso A B D F C).inv.app P) ≫
      (derivedComposeWithComputation A D C E Q.obj Q.property
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P)).hom ≫ k ≫
      (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).map
        (derivedComposeWithComputation A B C E Q'.obj Q'.property P).inv) hh

/-- 外側右制限の比較を、右K-flat後因子にも自然な自然同型へ束ねる。 -/
def rightRestrictionKFlatComposeIso :
    rightRestrictionKFlatComposeSource A B D C E F ≅
      rightRestrictionKFlatComposeTarget A B D C E F :=
  NatIso.ofComponents (derivedComposeWithRightRestrictionIso A B D C E F) (by
    intro Q Q' g
    exact derivedComposeWithRightRestrictionIso_naturality A B D C E F g)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleRightRestrictionFamily

/-! ## BimoduleRightRestrictionFull（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRightRestrictionFull.lean） -/

/-! # 外側の右dg作用制限と両変数の全導来合成の比較

## 概要
外側の右dg作用制限と両変数の全導来合成の比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleRightRestrictionFull
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D B)
  (hE : localHomKFlat A E)

/-- 前因子の外側右作用を既存の導来制限で制限してから合成する関手族。 -/
def rightRestrictionDerivedComposeSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D E) :=
  derivedBimoduleComposeFunctor A D C E hE ⋙
    (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))

/-- 合成後の外側右作用を既存の導来制限で制限する関手族。 -/
def rightRestrictionDerivedComposeTarget : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D E) :=
  derivedBimoduleComposeFunctor A B C E hE ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A D E B E F (DGFunctor.id E))

def rightRestrictionDerivedComposeSourceBaseIso :
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        rightRestrictionDerivedComposeSource A B D C E F hE ≅
      rightRestrictionKFlatComposeSource A B D C E F :=
  Functor.isoWhiskerRight (rightKFlatComposePresentationIso A C E hE D)
    ((whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C)))

def rightRestrictionDerivedComposeTargetBaseIso :
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        rightRestrictionDerivedComposeTarget A B D C E F hE ≅
      rightRestrictionKFlatComposeTarget A B D C E F :=
  Functor.isoWhiskerRight (rightKFlatComposePresentationIso A C E hE B)
    ((whiskeringRight _ _ _).obj (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)))

/-- 外側右作用の制限は、両変数の全導来合成と自然に可換する。 -/
def derivedBimoduleComposeRightRestrictionIso :
    rightRestrictionDerivedComposeSource A B D C E F hE ≅
      rightRestrictionDerivedComposeTarget A B D C E F hE :=
  rightKFlatDerivedIsoOfPrecomp A C E hE _ _
    (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE ≪≫
      rightRestrictionKFlatComposeIso A B D C E F ≪≫
        (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).symm)

/-- 任意の指定右K-flat後因子上で、移送前の固定モデル比較を回復する。 -/
lemma derivedBimoduleComposeRightRestrictionIso_app_rightKFlat
    (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) =
      (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q ≫
        (derivedComposeWithRightRestrictionIso A B D C E F Q).hom ≫
          (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).inv.app Q := by
  unfold derivedBimoduleComposeRightRestrictionIso
  rw [rightKFlatDerivedIsoOfPrecomp_hom_app]
  rfl

lemma derivedBimoduleComposeRightRestrictionIso_model_square
    (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) ≫
        (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app Q =
      (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q ≫
        (derivedComposeWithRightRestrictionIso A B D C E F Q).hom := by
  rw [derivedBimoduleComposeRightRestrictionIso_app_rightKFlat]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (fun k =>
    (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q ≫ k)
    (Category.comp_id (derivedComposeWithRightRestrictionIso A B D C E F Q).hom)

/-- 指定モデル上の同じsquareを満たす全導来比較の自然変換は一意。 -/
lemma derivedBimoduleComposeRightRestriction_hom_unique
    {α : rightRestrictionDerivedComposeSource A B D C E F hE ⟶
      rightRestrictionDerivedComposeTarget A B D C E F hE}
    (h : ∀ Q : RightKFlatBimoduleCategory A C E,
      α.app ((bimoduleToDerived A C E).obj Q.obj) ≫
          (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app Q =
        (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q ≫
          (derivedComposeWithRightRestrictionIso A B D C E F Q).hom) :
    α = (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom := by
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  apply (cancel_mono
    ((rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app Q)).mp
  exact (h Q).trans
    (derivedBimoduleComposeRightRestrictionIso_model_square A B D C E F hE Q).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleRightRestrictionFull

/-! ## BimoduleRightRestrictionResolution（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRightRestrictionResolution.lean） -/

/-! # 外側右制限の全導来比較を任意の指定K-flat解像度で計算する

## 概要
外側右制限の全導来比較を任意の指定K-flat解像度で計算する。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleRightRestrictionResolution
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D B)
  (hE : localHomKFlat A E) (Q : BimoduleCategory A C E)
  (R : RightKFlatBimoduleCategory A C E) (q : R.obj ⟶ Q)
  (hq : BimoduleCategory.quasiIso A C E q)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D E B E F (DGFunctor.id E)

/-- 右K-flatモデルでの前合成表示は、既存の固定因子計算同型そのもの。 -/
lemma rightKFlatComposePresentationIso_hom_app :
    (rightKFlatComposePresentationIso A C E hE B).hom.app R =
      (derivedBimoduleComposeKFlatIso A B C E hE R).hom := by
  simp only [rightKFlatComposePresentationIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    eqToHom_app]
  change (derivedBimoduleComposeFunctor A B C E hE).map (𝟙 _) ≫
    (derivedBimoduleComposeKFlatIso A B C E hE R).hom ≫ 𝟙 _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- 全導来外側右制限比較と、任意の指定右K-flat解像度の計算同型とのsquare。 -/
lemma derivedBimoduleComposeRightRestrictionIso_resolution_square :
    (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q) ≫
      whiskerRight (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom RO =
    whiskerLeft RI (derivedBimoduleComposeResolutionComputation A D C E hE Q R q hq).hom ≫
      (derivedComposeWithRightRestrictionIso A B D C E F R).hom := by
  let S := rightRestrictionDerivedComposeSource A B D C E F hE
  let T := rightRestrictionDerivedComposeTarget A B D C E F hE
  let u := (bimoduleToDerived A C E).map q
  have hn := (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.naturality u
  have hs := congrArg (fun k => whiskerLeft RI k)
    (derivedBimoduleComposeResolutionComputation_fac A D C E hE Q R q hq)
  have ht := congrArg (fun k => whiskerRight k RO)
    (derivedBimoduleComposeResolutionComputation_fac A B C E hE Q R q hq)
  apply (Iso.cancel_iso_hom_left (S.mapIso (bimoduleDerivedIso A C E q hq)) _ _).1
  change S.map u ≫ (_ ≫ _) = S.map u ≫ (_ ≫ _)
  rw [← Category.assoc, hn, Category.assoc]
  have ht' : T.map u ≫
      whiskerRight (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom RO =
    (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app R := by
    simpa only [S, T, u, whiskeringRight_obj_map, rightRestrictionDerivedComposeTarget,
      rightRestrictionDerivedComposeTargetBaseIso,
      Functor.comp_map, Functor.isoWhiskerRight_hom, whiskerRight_app,
      rightKFlatComposePresentationIso_hom_app, whiskerRight_comp] using ht
  rw [ht', ← Category.assoc]
  have hs' : S.map u ≫
      whiskerLeft RI (derivedBimoduleComposeResolutionComputation A D C E hE Q R q hq).hom =
    (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app R := by
    simpa only [S, T, u, whiskeringLeft_obj_map, rightRestrictionDerivedComposeSource,
      rightRestrictionDerivedComposeSourceBaseIso,
      Functor.comp_map, Functor.isoWhiskerRight_hom, whiskerRight_app,
      rightKFlatComposePresentationIso_hom_app, whiskerLeft_comp] using hs
  rw [hs']
  exact derivedBimoduleComposeRightRestrictionIso_model_square A B D C E F hE R

/-- 元の前因子上では、任意解像度による全導来外側比較は通常の比較射に計算できる。 -/
lemma derivedBimoduleComposeRightRestrictionIso_resolution_app_calc
    (P : BimoduleCategory A B C) :
    (derivedBimoduleComposeResolutionComputation A D C E hE Q R q hq).inv.app
        ((bimoduleToDerived A D C).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P)) ≫
      ((derivedBimoduleComposeFunctor A D C E hE).obj ((bimoduleToDerived A C E).obj Q)).map
        ((middleRightRestrictionDerivedIso A B D F C).hom.app P) ≫
      ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q)).app ((bimoduleToDerived A B C).obj P) ≫
      (RO).map ((derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom.app
        ((bimoduleToDerived A B C).obj P)) =
    (bimoduleToDerived A D E).map (composeRightRestrictionIso A B D C E F P R.obj).hom ≫
      (middleRightRestrictionDerivedIso A B D F E).hom.app
        ((composeWith A B C E R.obj).obj P) := by
  let cD := derivedBimoduleComposeResolutionComputation A D C E hE Q R q hq
  let cB := derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq
  let e := (middleRightRestrictionDerivedIso A B D F C).app P
  let V := derivedComposeWith A D C E R.obj R.property
  have hn := cD.inv.naturality e.hom
  have hc := NatTrans.congr_app
    (derivedBimoduleComposeRightRestrictionIso_resolution_square A B D C E F hE Q R q hq)
    ((bimoduleToDerived A B C).obj P)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hc
  have h : cD.inv.app ((RI).obj ((bimoduleToDerived A B C).obj P)) ≫
      ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q)).app ((bimoduleToDerived A B C).obj P) ≫
      (RO).map (cB.hom.app ((bimoduleToDerived A B C).obj P)) =
    (derivedComposeWithRightRestrictionIso A B D C E F R).hom.app
      ((bimoduleToDerived A B C).obj P) := by
    rw [hc]
    exact (cD.app ((RI).obj ((bimoduleToDerived A B C).obj P))).inv_hom_id_assoc _
  change cD.inv.app ((BimoduleCategory.middleRightRestrictionFunctor A B D C F ⋙
    bimoduleToDerived A D C).obj P) ≫
    ((derivedBimoduleComposeFunctor A D C E hE).obj
      ((bimoduleToDerived A C E).obj Q)).map e.hom ≫ _ ≫ _ = _
  erw [← Category.assoc (cD.inv.app _), ← hn, Category.assoc, h]
  rw [derivedComposeWithRightRestrictionIso_hom_app_calc]
  change V.map e.hom ≫ (V.map e.inv ≫ 𝟙 _ ≫ _ ≫ _ ≫ (RO).map (𝟙 _)) = _
  rw [← Category.assoc, ← V.map_comp, e.hom_inv_id, V.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleRightRestrictionResolution

/-! ## BimoduleMiddleOutputRestriction（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleOutputRestriction.lean） -/

/-! # 中間比較のモデル計算を既存の出力側導来制限へ移す

## 概要
中間比較のモデル計算を既存の出力側導来制限へ移す。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleOutputRestriction
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (K : Type s) [DGCategory A K] [Small.{u} K] (G : DGFunctor A K B)
  (hE : localHomKFlat A E) (P : BimoduleCategory A B C)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "S" => BimoduleCategory.of A B E
  (compose A B D E (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))
    (BimoduleCategory.underlying A D E R.obj))
local notation "T" => BimoduleCategory.of A B E
  (compose A B C E (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A C E Q.obj))
local notation "RG" => derivedBimoduleRestriction A K E B E G (DGFunctor.id E)

/-- source表示と実際の中間比較を続ける経路は、通常の計算射を出力で制限する経路に一致する。 -/
lemma derivedMiddleRestrictionComparison_output_restriction :
    (middleRightRestrictionDerivedIso A B K G E).hom.app S ≫
      (RG).map
        ((middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).inv ≫
          derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq ≫
          (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom) =
    (bimoduleToDerived A K E).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B K E G).map
          (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) ≫
      (middleRightRestrictionDerivedIso A B K G E).hom.app T := by
  have h := derivedMiddleRestrictionComparison_calculation A B C D E F hE P Q R q hq
  have hh := congrArg (fun k =>
    (middleRightRestrictionDerivedIso A B K G E).hom.app S ≫ (RG).map k) h
  exact hh.trans ((middleRightRestrictionDerivedIso A B K G E).hom.naturality
    (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)).symm

/-- 同じ表示移送を、source計算・中間比較・target計算の各像に分けた式。 -/
lemma derivedMiddleRestrictionComparison_output_restriction_expanded :
    (middleRightRestrictionDerivedIso A B K G E).hom.app S ≫
      (RG).map (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).inv ≫
      (RG).map (derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq) ≫
      (RG).map (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom =
    (bimoduleToDerived A K E).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B K E G).map
          (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) ≫
      (middleRightRestrictionDerivedIso A B K G E).hom.app T := by
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    derivedMiddleRestrictionComparison_output_restriction A B C D E F K G hE P Q R q hq

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleOutputRestriction

/-! ## BimoduleMiddleSourceIdentification（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleSourceIdentification.lean） -/

/-! # 中間圏比較のsourceと既存の導来制限・導来合成の比較

## 概要
中間圏比較のsourceと既存の導来制限・導来合成の比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleSourceIdentification
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

/-- 既存の導来制限と導来合成だけで表した中間圏比較のsource。 -/
def middleRestrictionDerivedSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  derivedBimoduleRestriction A D E C E F (DGFunctor.id E) ⋙
    derivedBimoduleComposeFunctor A B D E hE ⋙
      (whiskeringLeft _ _ _).obj
        (derivedBimoduleRestriction A B D B C (DGFunctor.id B) F)

/-- 閉零の後因子上で、前因子の局所化をまだ延長しないsource関手族。 -/
def middleClosedSourceFunctor : BimoduleCategory A C E ⥤
    (BimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  (BimoduleCategory.middleRightRestrictionFunctor A C D E F ⋙ bimoduleToDerived A D E) ⋙
    derivedBimoduleComposeFunctor A B D E hE ⋙
      (whiskeringLeft _ _ _).obj
        (BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ bimoduleToDerived A B D)

/-- 両因子の閉零射に自然な、既存の導来制限と導来合成へのsource表示比較。 -/
def middleClosedSourceIdentification :
    middleClosedSourceFunctor A B C D E F hE ≅
      bimoduleToDerived A C E ⋙ middleRestrictionDerivedSource A B C D E F hE ⋙
        (whiskeringLeft _ _ _).obj (bimoduleToDerived A B C) :=
  Functor.isoWhiskerLeft
      (BimoduleCategory.middleRightRestrictionFunctor A C D E F ⋙ bimoduleToDerived A D E)
      (Functor.isoWhiskerLeft (derivedBimoduleComposeFunctor A B D E hE)
        ((whiskeringLeft _ _ _).mapIso (middleLeftRestrictionDerivedIso A B C D F))) ≪≫
    Functor.isoWhiskerRight (middleRightRestrictionDerivedIso A C D F E)
      (derivedBimoduleComposeFunctor A B D E hE ⋙
        (whiskeringLeft _ _ _).obj (bimoduleToDerived A B C ⋙
          derivedBimoduleRestriction A B D B C (DGFunctor.id B) F))

/-- 閉零の前因子上で、既存のsourceを導来制限と導来合成へ比較する。 -/
def middleDerivedSourceFamilyIdentification (Q : RightKFlatBimoduleCategory A C E) :
    middleDerivedSourceFamily A B C D E F hE Q ≅
      bimoduleToDerived A B C ⋙
        (middleRestrictionDerivedSource A B C D E F hE).obj
          ((bimoduleToDerived A C E).obj Q.obj) :=
  (middleClosedSourceIdentification A B C D E F hE).app Q.obj

instance middleRestrictionSourceTarget_lifting (Q : RightKFlatBimoduleCategory A C E) :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (bimoduleToDerived A B C ⋙ (middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q.obj))
      ((middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q.obj)) := ⟨Iso.refl _⟩

/-- 指定右K-flat後因子について、前因子の全導来圏上のsourceを既存APIへ同定する。 -/
def middleDerivedSourceLiftIdentification (Q : RightKFlatBimoduleCategory A C E) :
    middleDerivedSourceLift A B C D E F hE Q ≅
      (middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q.obj) :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (middleDerivedSourceFamily A B C D E F hE Q)
    (bimoduleToDerived A B C ⋙ (middleRestrictionDerivedSource A B C D E F hE).obj
      ((bimoduleToDerived A C E).obj Q.obj))
    (middleDerivedSourceLift A B C D E F hE Q)
    ((middleRestrictionDerivedSource A B C D E F hE).obj
      ((bimoduleToDerived A C E).obj Q.obj))
    (middleDerivedSourceFamilyIdentification A B C D E F hE Q)

lemma middleRestrictionSourceTargetMap_lift
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (bimoduleToDerived A B C ⋙ (middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q.obj))
      (bimoduleToDerived A B C ⋙ (middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q'.obj))
      ((middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q.obj))
      ((middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q'.obj))
      (whiskerLeft (bimoduleToDerived A B C)
        ((middleRestrictionDerivedSource A B C D E F hE).map
          ((bimoduleToDerived A C E).map g.hom))) =
      (middleRestrictionDerivedSource A B C D E F hE).map
        ((bimoduleToDerived A C E).map g.hom) := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  rw [Localization.liftNatTrans_app]
  change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- sourceの同定は後因子の任意の閉零射に関しても自然。 -/
lemma middleDerivedSourceLiftIdentification_naturality
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedSourceLiftMap A B C D E F hE g ≫
        (middleDerivedSourceLiftIdentification A B C D E F hE Q').hom =
      (middleDerivedSourceLiftIdentification A B C D E F hE Q).hom ≫
        (middleRestrictionDerivedSource A B C D E F hE).map
          ((bimoduleToDerived A C E).map g.hom) := by
  rw [← middleRestrictionSourceTargetMap_lift A B C D E F hE g]
  unfold middleDerivedSourceLiftMap middleDerivedSourceLiftIdentification
  simp only [Localization.liftNatIso_hom, Localization.comp_liftNatTrans]
  congr 1
  exact (middleClosedSourceIdentification A B C D E F hE).hom.naturality g.hom

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleSourceIdentification

/-! ## BimoduleMiddleSourceFull（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleSourceFull.lean） -/

/-! # 全導来中間比較を既存の導来制限・導来合成のsourceに移す

## 概要
全導来中間比較を既存の導来制限・導来合成のsourceに移す。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleSourceFull
universe u v w z t

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

/-- 後因子の右K-flat部分圏上でのsource表示の自然同型。 -/
def middleSourceKFlatIdentification :
    middleDerivedSourceKFlatFunctor A B C D E F hE ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        middleRestrictionDerivedSource A B C D E F hE :=
  NatIso.ofComponents (middleDerivedSourceLiftIdentification A B C D E F hE)
    (fun g => middleDerivedSourceLiftIdentification_naturality A B C D E F hE g)

lemma middleSourceKFlatTarget_fac :
    rightKFlatToDerived A C E ⋙
        (rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE) =
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        middleRestrictionDerivedSource A B C D E F hE := by
  rw [← Functor.assoc, rightKFlatDerivedInclusion_fac]
  rfl

instance middleSourceKFlatTarget_lifting :
    Localization.Lifting (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
      (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        middleRestrictionDerivedSource A B C D E F hE)
      (rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE) :=
  ⟨eqToIso (middleSourceKFlatTarget_fac A B C D E F hE)⟩

/-- 後因子の指定準同型の局所化上でのsource表示の自然同型。 -/
def middleRightKFlatSourceIdentification :
    middleRightKFlatLocalizedSource A B C D E F hE ≅
      rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE :=
  Localization.liftNatIso (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
    (middleDerivedSourceKFlatFunctor A B C D E F hE)
    (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
      middleRestrictionDerivedSource A B C D E F hE)
    (middleRightKFlatLocalizedSource A B C D E F hE)
    (rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE)
    (middleSourceKFlatIdentification A B C D E F hE)

/-- 両変数の全導来圏上で、比較のsourceを既存の導来制限と導来合成へ同定する。 -/
def middleFullDerivedSourceIdentification :
    middleFullDerivedSource A B C D E F hE ≅
      middleRestrictionDerivedSource A B C D E F hE :=
  Functor.isoWhiskerLeft (derivedRightKFlatReplacement A C E hE)
      (middleRightKFlatSourceIdentification A B C D E F hE) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightKFlatReplacementCounitIso A C E hE)
      (middleRestrictionDerivedSource A B C D E F hE) ≪≫ Functor.leftUnitor _

/-- 既存の導来制限と導来合成の間の、両変数の全導来射に自然な中間圏比較。 -/
def derivedMiddleRestrictionNatTrans :
    middleRestrictionDerivedSource A B C D E F hE ⟶
      derivedBimoduleComposeFunctor A B C E hE :=
  (middleFullDerivedSourceIdentification A B C D E F hE).inv ≫
    middleFullDerivedComparison A B C D E F hE

lemma derivedMiddleRestrictionNatTrans_transport :
    (middleFullDerivedSourceIdentification A B C D E F hE).hom ≫
        derivedMiddleRestrictionNatTrans A B C D E F hE =
      middleFullDerivedComparison A B C D E F hE := by
  unfold derivedMiddleRestrictionNatTrans
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- source表示同型による移送を各導来対象で計算する。 -/
lemma derivedMiddleRestrictionNatTrans_app
    (Q : DerivedBimoduleCategory A C E) (P : DerivedBimoduleCategory A B C) :
    ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q).app P =
      ((middleFullDerivedSourceIdentification A B C D E F hE).inv.app Q).app P ≫
        ((middleFullDerivedComparison A B C D E F hE).app Q).app P := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleSourceFull
