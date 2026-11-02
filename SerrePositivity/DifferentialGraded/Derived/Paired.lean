module

public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddle
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Restriction
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeft
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Derived.Bimodule
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.FunctorCoherence

/-!
# Derived.Paired

## 概要
8 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## AssociatorSecondMiddleRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorSecondMiddleRestrictionCoherence.lean） -/

/-! # 全導来三因子に対する第二中間制限と結合子のcoherence

## 概要
全導来三因子に対する第二中間制限と結合子のcoherence。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestrictionCoherence
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D) (hT : localHomKFlat A T)

local notation "LQ" => derivedBimoduleRestriction A C D C E (DGFunctor.id C) F
local notation "RR" => derivedBimoduleRestriction A D T E T F (DGFunctor.id T)

/-- 指定K-flatモデル上の一致を後二つの全導来変数へ持ち上げる。 -/
lemma secondMiddleRestrictionAssociatorPaths_eq :
    secondMiddleRestrictionAssociatorLeftPath A B C D E T F hE hD hT =
      secondMiddleRestrictionAssociatorRightPath A B C D E T F hD hT := by
  apply rightKFlatDerivedNatTrans_ext A E T hT
  intro R
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  rw [secondMiddleRestrictionAssociatorLeftPath_app, secondMiddleRestrictionAssociatorRightPath_app]
  exact derivedBimoduleAssociator_secondMiddleRestriction_rightKFlat A B C D E T F hE hD hT Q R

/-- 任意の導来三因子で、第二中間圏の全導来比較は実際の全導来結合子と可換。 -/
lemma derivedBimoduleAssociator_secondMiddleRestriction
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E T) :
    whiskerRight ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app Q)
        ((derivedBimoduleComposeFunctor A B D T hT).obj ((RR).obj R)) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q)
        ((derivedMiddleRestrictionNatTrans A B E D T F hT).app R) ≫
      (derivedBimoduleAssociator A B C E T hE hT Q R).hom =
    (derivedBimoduleAssociator A B C D T hD hT ((LQ).obj Q) ((RR).obj R)).hom ≫
      (derivedBimoduleComposeFunctor A B C T hT).map
        (((derivedMiddleRestrictionNatTrans A C E D T F hT).app R).app Q) := by
  have h := NatTrans.congr_app
    (NatTrans.congr_app (secondMiddleRestrictionAssociatorPaths_eq A B C D E T F hE hD hT) R) Q
  simpa only [secondMiddleRestrictionAssociatorLeftPath_app,
    secondMiddleRestrictionAssociatorRightPath_app] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestrictionCoherence

/-! ## LeftUnitOuterRestriction（旧 SerrePositivity/DifferentialGraded/Derived/LeftUnitOuterRestriction.lean） -/

/-! # 外側左制限の全導来比較は左単位子を保つ

## 概要
外側左制限の全導来比較は左単位子を保つ。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftUnitOuterRestriction
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)
  (hC : localHomKFlat A C) (hD : localHomKFlat A D)

local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F

/-- 実際の全導来左制限比較の逆と、制限した左単位子を続ける経路。 -/
def leftUnitOuterLeftRestrictionComparison :
    L ⋙ derivedBimoduleLeftUnitFunctor A B D hD ⟶ L :=
  whiskerRight (derivedBimoduleComposeLeftRestrictionIso A B B C D F hC hD).inv
      ((CategoryTheory.evaluation _ _).obj
        ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj)) ≫
    whiskerRight (derivedBimoduleLeftUnitIso A B C hC).hom L

lemma leftUnitOuterLeftRestrictionComparison_app (Q : DerivedBimoduleCategory A B C) :
    (leftUnitOuterLeftRestrictionComparison A B C D F hC hD).app Q =
      ((derivedBimoduleComposeLeftRestrictionIso A B B C D F hC hD).inv.app Q).app
        ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj) ≫
        (L).map ((derivedBimoduleLeftUnitIso A B C hC).hom.app Q) := rfl

/-- 指定K-flat後因子では、既存の制限表示で挟んだ左単位子に計算される。 -/
lemma leftUnitOuterLeftRestrictionComparison_model (Q : RightKFlatBimoduleCategory A B C) :
    (leftUnitOuterLeftRestrictionComparison A B C D F hC hD).app
        ((bimoduleToDerived A B C).obj Q.obj) =
    (derivedBimoduleLeftUnitFunctor A B D hD).map
        ((middleLeftRestrictionDerivedIso A B C D F).inv.app Q.obj) ≫
      (derivedBimoduleLeftUnitIso A B D hD).hom.app
        ((bimoduleToDerived A B D).obj ((rightKFlatLeftRestriction A B C D F).obj Q).obj) ≫
      (middleLeftRestrictionDerivedIso A B C D F).hom.app Q.obj := by
  let LQ := (rightKFlatLeftRestriction A B C D F).obj Q
  let I := (rightKFlatDiagonal A B).obj
  let u := (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C Q.obj)).hom
  have hn := (middleLeftRestrictionDerivedIso A B C D F).hom.naturality u
  have hs := congrArg ((bimoduleToDerived A B D).map)
    (leftBimoduleUnitIso_leftRestriction A B C D F Q.obj)
  simp only [CategoryTheory.Functor.map_comp] at hs
  rw [leftUnitOuterLeftRestrictionComparison_app,
    derivedBimoduleLeftUnitIso_kFlat_base_app A B C hC Q,
    derivedBimoduleLeftUnitIso_kFlat_base_app A B D hD LQ,
    CategoryTheory.Functor.map_comp]
  have hc := derivedBimoduleComposeLeftRestrictionIso_inv_base_calculation
    A B B C D F hC hD Q I
  rw [← Category.assoc, hc]
  simp only [Category.assoc]
  simp only [Functor.comp_map] at hn
  erw [← hn]
  dsimp only [u, I] at *
  erw [reassoc_of% hs]
  rfl

/-- 指定K-flat後因子上で、外側左制限の単位経路は制限後の実際の左単位子と一致する。 -/
lemma leftUnitOuterLeftRestrictionComparison_kFlat (Q : RightKFlatBimoduleCategory A B C) :
    (leftUnitOuterLeftRestrictionComparison A B C D F hC hD).app
        ((bimoduleToDerived A B C).obj Q.obj) =
    (derivedBimoduleLeftUnitIso A B D hD).hom.app
      ((L).obj ((bimoduleToDerived A B C).obj Q.obj)) := by
  rw [leftUnitOuterLeftRestrictionComparison_model]
  have hn := (derivedBimoduleLeftUnitIso A B D hD).hom.naturality
    ((middleLeftRestrictionDerivedIso A B C D F).inv.app Q.obj)
  have h := congrArg (fun k => k ≫
    (middleLeftRestrictionDerivedIso A B C D F).hom.app Q.obj) hn
  simp only [Functor.id_map, Category.assoc] at h
  erw [Iso.inv_hom_id_app, Category.comp_id] at h
  exact h

/-- 外側左制限の全導来比較と左単位子の可換square。Fの準同値性は不要。 -/
lemma leftUnitOuterLeftRestrictionComparison_eq :
    leftUnitOuterLeftRestrictionComparison A B C D F hC hD =
      whiskerLeft L (derivedBimoduleLeftUnitIso A B D hD).hom := by
  apply rightKFlatDerivedNatTrans_ext A B C hC
  intro Q
  exact leftUnitOuterLeftRestrictionComparison_kFlat A B C D F hC hD Q

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end LeftUnitOuterRestriction

/-! ## PairedRestrictionIdentification（旧 SerrePositivity/DifferentialGraded/Derived/PairedRestrictionIdentification.lean） -/

/-! # 両端制限と既存の積dg圏表示による導来制限の比較

## 概要
両端制限と既存の積dg圏表示による導来制限の比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PairedRestrictionIdentification
universe u v w z t

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory BimoduleTensorModule
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A D B) (G : DGFunctor A E C)

/-- 直接両端制限は、既存の積dg圏表示によるbimodule制限に自然同型。 -/
def pairedRestrictionIso :
    BimoduleCategory.pairedRestrictionFunctor A B C D E F G ≅
      bimoduleRestriction A D E B C F G :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.pairedRestrictionFunctor A B C D E F G)
      (rightModuleCounitIso A D E).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pairedRestrictionPresentationIso A B C D E F G)
      (rightModuleBimoduleEquivalence A D E).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (rightModuleInverseIso A B C)
      (moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (bimoduleRestrictionIndex A D E B C F G) ⋙
          (rightModuleBimoduleEquivalence A D E).functor)

/-- 直接両端制限と既存の全導来制限の表示square。 -/
def pairedRestrictionDerivedIso :
    BimoduleCategory.pairedRestrictionFunctor A B C D E F G ⋙ bimoduleToDerived A D E ≅
      bimoduleToDerived A B C ⋙ derivedBimoduleRestriction A D E B C F G :=
  Functor.isoWhiskerRight (pairedRestrictionIso A B C D E F G) (bimoduleToDerived A D E) ≪≫
    (eqToIso (derivedBimoduleRestriction_fac A D E B C F G)).symm

/-- 左、次に右の二つの既存導来制限の、直接制限からの表示。 -/
def pairedRestrictionPartialPresentationIso :
    BimoduleCategory.pairedRestrictionFunctor A B C D E F G ⋙ bimoduleToDerived A D E ≅
      bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A B E B C (DGFunctor.id B) G ⋙
          derivedBimoduleRestriction A D E B E F (DGFunctor.id E)) :=
  Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C E G)
      (middleRightRestrictionDerivedIso A B D F E) ≪≫
    Functor.isoWhiskerRight (middleLeftRestrictionDerivedIso A B C E G)
      (derivedBimoduleRestriction A D E B E F (DGFunctor.id E))

def pairedRestrictionPartialPreIso :
    bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A B E B C (DGFunctor.id B) G ⋙
          derivedBimoduleRestriction A D E B E F (DGFunctor.id E)) ≅
      bimoduleToDerived A B C ⋙ derivedBimoduleRestriction A D E B C F G :=
  (pairedRestrictionPartialPresentationIso A B C D E F G).symm ≪≫
    pairedRestrictionDerivedIso A B C D E F G

/-- 左制限、右制限の順の合成は、既存の同時導来制限へ自然に比較できる。 -/
def pairedRestrictionPartialDerivedIso :
    derivedBimoduleRestriction A B E B C (DGFunctor.id B) G ⋙
        derivedBimoduleRestriction A D E B E F (DGFunctor.id E) ≅
      derivedBimoduleRestriction A D E B C F G :=
  bimoduleDerivedIsoOfPrecomp A B C _ _ (pairedRestrictionPartialPreIso A B C D E F G)

lemma pairedRestrictionPartialDerivedIso_hom_app (P : BimoduleCategory A B C) :
    (pairedRestrictionPartialDerivedIso A B C D E F G).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (pairedRestrictionPartialPreIso A B C D E F G).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

/-- 右、次に左の二つの既存導来制限の、直接制限からの表示。 -/
def pairedRestrictionReversePresentationIso :
    (BimoduleCategory.middleRightRestrictionFunctor A B D C F ⋙
        BimoduleCategory.middleLeftRestrictionFunctor A D C E G) ⋙ bimoduleToDerived A D E ≅
      bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A D C B C F (DGFunctor.id C) ⋙
          derivedBimoduleRestriction A D E D C (DGFunctor.id D) G) :=
  Functor.isoWhiskerLeft (BimoduleCategory.middleRightRestrictionFunctor A B D C F)
      (middleLeftRestrictionDerivedIso A D C E G) ≪≫
    Functor.isoWhiskerRight (middleRightRestrictionDerivedIso A B D F C)
      (derivedBimoduleRestriction A D E D C (DGFunctor.id D) G)

def pairedRestrictionReversePreIso :
    bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A D C B C F (DGFunctor.id C) ⋙
          derivedBimoduleRestriction A D E D C (DGFunctor.id D) G) ≅
      bimoduleToDerived A B C ⋙ derivedBimoduleRestriction A D E B C F G :=
  (pairedRestrictionReversePresentationIso A B C D E F G).symm ≪≫
    Functor.isoWhiskerRight
      (BimoduleCategory.pairedRestrictionInterchangeIso A B C D E F G).symm
      (bimoduleToDerived A D E) ≪≫
    pairedRestrictionDerivedIso A B C D E F G

/-- 右制限、左制限の順も、同じ既存の同時導来制限へ自然に比較できる。 -/
def pairedRestrictionReverseDerivedIso :
    derivedBimoduleRestriction A D C B C F (DGFunctor.id C) ⋙
        derivedBimoduleRestriction A D E D C (DGFunctor.id D) G ≅
      derivedBimoduleRestriction A D E B C F G :=
  bimoduleDerivedIsoOfPrecomp A B C _ _ (pairedRestrictionReversePreIso A B C D E F G)

lemma pairedRestrictionReverseDerivedIso_hom_app (P : BimoduleCategory A B C) :
    (pairedRestrictionReverseDerivedIso A B C D E F G).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (pairedRestrictionReversePreIso A B C D E F G).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

end SerrePositivity.DifferentialGraded
end

end PairedRestrictionIdentification

/-! ## PairedRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Derived/PairedRestrictionCoherence.lean） -/

/-! # 既存の両端導来制限の恒等・合成比較とモデル計算

## 概要
既存の両端導来制限の恒等・合成比較とモデル計算。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PairedRestrictionCoherence
universe u v w z t s r

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

def pairedRestrictionIdDerivedPreIso :
    bimoduleToDerived A B C ⋙
        derivedBimoduleRestriction A B C B C (DGFunctor.id B) (DGFunctor.id C) ≅
      bimoduleToDerived A B C ⋙ 𝟭 (DerivedBimoduleCategory A B C) :=
  (pairedRestrictionDerivedIso A B C B C (DGFunctor.id B) (DGFunctor.id C)).symm ≪≫
    Functor.isoWhiskerRight (BimoduleCategory.pairedRestrictionIdIso A B C)
      (bimoduleToDerived A B C)

/-- 既存の同時導来制限の恒等比較。 -/
def pairedRestrictionIdDerivedIso :
    derivedBimoduleRestriction A B C B C (DGFunctor.id B) (DGFunctor.id C) ≅
      𝟭 (DerivedBimoduleCategory A B C) :=
  bimoduleDerivedIsoOfPrecomp A B C _ _ (pairedRestrictionIdDerivedPreIso A B C)

lemma pairedRestrictionIdDerivedIso_hom_app (P : BimoduleCategory A B C) :
    (pairedRestrictionIdDerivedIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
      (pairedRestrictionIdDerivedPreIso A B C).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

variable (E : Type z) [DGCategory A E] [Small.{u} E]
  (L : Type t) [DGCategory A L] [Small.{u} L]
  (D : Type s) [DGCategory A D] [Small.{u} D]
  (K : Type r) [DGCategory A K] [Small.{u} K]
  (F : DGFunctor A D E) (G : DGFunctor A E B)
  (H : DGFunctor A K L) (I : DGFunctor A L C)

def pairedRestrictionCompDerivedPreIso :
    bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A E L B C G I ⋙
          derivedBimoduleRestriction A D K E L F H) ≅
      bimoduleToDerived A B C ⋙
        derivedBimoduleRestriction A D K B C (F.comp G) (H.comp I) :=
  Functor.isoWhiskerRight (pairedRestrictionDerivedIso A B C E L G I).symm
      (derivedBimoduleRestriction A D K E L F H) ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.pairedRestrictionFunctor A B C E L G I)
      (pairedRestrictionDerivedIso A E L D K F H).symm ≪≫
    Functor.isoWhiskerRight
      (BimoduleCategory.pairedRestrictionCompIso A B C E L D K F G H I)
      (bimoduleToDerived A D K) ≪≫
    pairedRestrictionDerivedIso A B C D K (F.comp G) (H.comp I)

/-- 二つの既存同時導来制限の合成を、合成dg関手による既存制限へ送る。 -/
def pairedRestrictionCompDerivedIso :
    derivedBimoduleRestriction A E L B C G I ⋙ derivedBimoduleRestriction A D K E L F H ≅
      derivedBimoduleRestriction A D K B C (F.comp G) (H.comp I) :=
  bimoduleDerivedIsoOfPrecomp A B C _ _
    (pairedRestrictionCompDerivedPreIso A B C E L D K F G H I)

lemma pairedRestrictionCompDerivedIso_hom_app (P : BimoduleCategory A B C) :
    (pairedRestrictionCompDerivedIso A B C E L D K F G H I).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (pairedRestrictionCompDerivedPreIso A B C E L D K F G H I).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

end SerrePositivity.DifferentialGraded
end

end PairedRestrictionCoherence

/-! ## DiagonalRestriction（旧 SerrePositivity/DifferentialGraded/Derived/DiagonalRestriction.lean） -/

/-! # 既存の同時導来制限に沿う対角bimoduleの比較

## 概要
既存の同時導来制限に沿う対角bimoduleの比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section DiagonalRestriction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- Hom写像を局所化し、既存の同時導来制限表示へ送る対角比較射。 -/
def derivedDiagonalRestrictionMap :
    (bimoduleToDerived A D D).obj (rightKFlatDiagonal A D).obj ⟶
      (derivedBimoduleRestriction A D D E E F F).obj
        ((bimoduleToDerived A E E).obj (rightKFlatDiagonal A E).obj) :=
  (bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D E F) ≫
    (pairedRestrictionDerivedIso A E E D D F F).hom.app (rightKFlatDiagonal A E).obj

/-- Homがすべて準同型なら、対角比較は既存の導来bimodule圏上の同型。 -/
def derivedDiagonalRestrictionIso (hF : HomQuasiIso F) :
    (bimoduleToDerived A D D).obj (rightKFlatDiagonal A D).obj ≅
      (derivedBimoduleRestriction A D D E E F F).obj
        ((bimoduleToDerived A E E).obj (rightKFlatDiagonal A E).obj) :=
  bimoduleDerivedIso A D D (Bimodule.diagonalRestrictionMap A D E F)
      ((Bimodule.diagonalRestrictionMap_quasiIso_iff A D E F).2 hF) ≪≫
    (pairedRestrictionDerivedIso A E E D D F F).app (rightKFlatDiagonal A E).obj

lemma derivedDiagonalRestrictionIso_hom (hF : HomQuasiIso F) :
    (derivedDiagonalRestrictionIso A D E F hF).hom = derivedDiagonalRestrictionMap A D E F := rfl

lemma derivedDiagonalRestrictionMap_isIso (hF : HomQuasiIso F) :
    IsIso (derivedDiagonalRestrictionMap A D E F) := by
  rw [← derivedDiagonalRestrictionIso_hom A D E F hF]
  infer_instance

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end DiagonalRestriction

/-! ## DiagonalRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Derived/DiagonalRestrictionCoherence.lean） -/

/-! # 既存の導来両端制限における対角比較の恒等・合成則

## 概要
既存の導来両端制限における対角比較の恒等・合成則。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section DiagonalRestrictionCoherence
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma derivedDiagonalRestrictionMap_id :
    derivedDiagonalRestrictionMap A D D (DGFunctor.id D) ≫
        (pairedRestrictionIdDerivedIso A D D).hom.app
          ((bimoduleToDerived A D D).obj (rightKFlatDiagonal A D).obj) = 𝟙 _ := by
  rw [pairedRestrictionIdDerivedIso_hom_app]
  change ((bimoduleToDerived A D D).map
      (Bimodule.diagonalRestrictionMap A D D (DGFunctor.id D)) ≫
    (pairedRestrictionDerivedIso A D D D D (DGFunctor.id D) (DGFunctor.id D)).hom.app _) ≫
    ((pairedRestrictionDerivedIso A D D D D (DGFunctor.id D) (DGFunctor.id D)).inv.app _ ≫
      (bimoduleToDerived A D D).map
        (BimoduleCategory.pairedRestrictionIdObjIso A D D
          (BimoduleCategory.of A D D (Bimodule.diagonal A D))).hom) =
      𝟙 ((bimoduleToDerived A D D).obj (BimoduleCategory.of A D D (Bimodule.diagonal A D)))
  rw [Category.assoc,
    Iso.hom_inv_id_app_assoc,
    ← CategoryTheory.Functor.map_comp,
    Bimodule.diagonalRestrictionMap_id, CategoryTheory.Functor.map_id]

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

lemma derivedDiagonalRestrictionMap_comp :
    derivedDiagonalRestrictionMap A D E F ≫
        (derivedBimoduleRestriction A D D E E F F).map
          (derivedDiagonalRestrictionMap A E T G) ≫
        (pairedRestrictionCompDerivedIso A T T E E D D F G F G).hom.app
          ((bimoduleToDerived A T T).obj (BimoduleCategory.of A T T (Bimodule.diagonal A T))) =
      derivedDiagonalRestrictionMap A D T (F.comp G) := by
  rw [pairedRestrictionCompDerivedIso_hom_app]
  let eF := pairedRestrictionDerivedIso A E E D D F F
  let eG := pairedRestrictionDerivedIso A T T E E G G
  let QD := bimoduleToDerived A D D
  let QE := bimoduleToDerived A E E
  let RF := derivedBimoduleRestriction A D D E E F F
  let rawF := BimoduleCategory.pairedRestrictionFunctor A E E D D F F
  let dG := Bimodule.diagonalRestrictionMap A E T G
  have hn : eF.hom.app (BimoduleCategory.of A E E (Bimodule.diagonal A E)) ≫ RF.map (QE.map dG) =
      QD.map (rawF.map dG) ≫ eF.hom.app
        ((BimoduleCategory.pairedRestrictionFunctor A T T E E G G).obj
          (BimoduleCategory.of A T T (Bimodule.diagonal A T))) := eF.hom.naturality dG |>.symm
  change (QD.map (Bimodule.diagonalRestrictionMap A D E F) ≫ eF.hom.app _) ≫
    RF.map (QE.map dG ≫ eG.hom.app _) ≫
    (RF.map (eG.inv.app _) ≫ eF.inv.app _ ≫
      QD.map (BimoduleCategory.pairedRestrictionCompObjIso A T T E E D D F G F G
        (BimoduleCategory.of A T T (Bimodule.diagonal A T))).hom ≫
      (pairedRestrictionDerivedIso A T T D D (F.comp G) (F.comp G)).hom.app _) =
    QD.map (Bimodule.diagonalRestrictionMap A D T (F.comp G)) ≫
      (pairedRestrictionDerivedIso A T T D D (F.comp G) (F.comp G)).hom.app _
  rw [RF.map_comp (QE.map dG) (eG.hom.app
    (BimoduleCategory.of A T T (Bimodule.diagonal A T)))]
  simp only [Category.assoc]
  rw [← RF.map_comp_assoc (eG.hom.app (BimoduleCategory.of A T T (Bimodule.diagonal A T)))
    (eG.inv.app (BimoduleCategory.of A T T (Bimodule.diagonal A T))),
    eG.hom_inv_id_app, RF.map_id, Category.id_comp]
  rw [← Category.assoc (eF.hom.app _), hn]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_app_assoc, ← QD.map_comp_assoc, ← QD.map_comp_assoc]
  rw [Category.assoc (Bimodule.diagonalRestrictionMap A D E F),
    Bimodule.diagonalRestrictionMap_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end DiagonalRestrictionCoherence

/-! ## BimoduleEndpointRestriction（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleEndpointRestriction.lean） -/

/-! # 合成の両端のdg圏の制限と全導来bimodule合成の比較

## 概要
合成の両端のdg圏の制限と全導来bimodule合成の比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleEndpointRestriction
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (K : Type s) [DGCategory A K] [Small.{u} K]
  (F : DGFunctor A D B) (H : DGFunctor A K E)
  (hE : localHomKFlat A E) (hK : localHomKFlat A K)

/-- 両因子の外側の作用をそれぞれ制限してから合成する既存導来関手族。 -/
def endpointRestrictionDerivedSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D K) :=
  derivedBimoduleRestriction A C K C E (DGFunctor.id C) H ⋙
    derivedBimoduleComposeFunctor A D C K hK ⋙
      (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))

/-- 合成後の両端を、既存の同時導来制限で制限する関手族。 -/
def endpointRestrictionDerivedTarget : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D K) :=
  derivedBimoduleComposeFunctor A B C E hE ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A D K B E F H)

/-- 外側左右の既存比較と両端制限の表示同型から作る、全導来合成比較。 -/
def derivedBimoduleComposeEndpointRestrictionIso :
    endpointRestrictionDerivedSource A B D C E K F H hK ≅
      endpointRestrictionDerivedTarget A B D C E K F H hE :=
  Functor.isoWhiskerLeft (derivedBimoduleRestriction A C K C E (DGFunctor.id C) H)
      (derivedBimoduleComposeRightRestrictionIso A B D C K F hK) ≪≫
    Functor.isoWhiskerRight
      (derivedBimoduleComposeLeftRestrictionIso A B C E K H hE hK).symm
      ((whiskeringRight _ _ _).obj
        (derivedBimoduleRestriction A D K B K F (DGFunctor.id K))) ≪≫
    Functor.isoWhiskerLeft (derivedBimoduleComposeFunctor A B C E hE)
      ((whiskeringRight _ _ _).mapIso (pairedRestrictionPartialDerivedIso A B E D K F H))

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleEndpointRestriction

/-! ## BimoduleSimultaneousRestriction（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleSimultaneousRestriction.lean） -/

/-! # 三つのdg圏を同時に制限した全導来bimodule合成比較

## 概要
三つのdg圏を同時に制限した全導来bimodule合成比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleSimultaneousRestriction
universe u v w z t s r

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (K : Type t) [DGCategory A K] [Small.{u} K]
  (E : Type s) [DGCategory A E] [Small.{u} E]
  (L : Type r) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D B) (G : DGFunctor A K C) (H : DGFunctor A L E)
  (hE : localHomKFlat A E) (hL : localHomKFlat A L)

/-- 三つのdg圏に沿う既存の同時導来制限を両因子へ適用してから合成するsource。 -/
def simultaneousRestrictionDerivedSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D L) :=
  derivedBimoduleRestriction A K L C E G H ⋙ derivedBimoduleComposeFunctor A D K L hL ⋙
    (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D K B C F G)

/-- 既存の外側左右制限を施したうえで、中間圏比較へ適用するsource表示。 -/
def simultaneousRestrictionMiddleSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D L) :=
  derivedBimoduleRestriction A C L C E (DGFunctor.id C) H ⋙
    middleRestrictionDerivedSource A D C K L G hL ⋙
      (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))

/-- 両因子の既存の同時制限を、外側制限と中間制限へ分ける独立のsource同型。 -/
def simultaneousRestrictionSourceIso :
    simultaneousRestrictionDerivedSource A B D C K E L F G H hL ≅
      simultaneousRestrictionMiddleSource A B D C K E L F G H hL :=
  Functor.isoWhiskerRight (pairedRestrictionPartialDerivedIso A C E K L G H).symm
      (derivedBimoduleComposeFunctor A D K L hL ⋙
        (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D K B C F G)) ≪≫
    Functor.isoWhiskerLeft
      (derivedBimoduleRestriction A C L C E (DGFunctor.id C) H ⋙
        derivedBimoduleRestriction A K L C L G (DGFunctor.id L) ⋙
          derivedBimoduleComposeFunctor A D K L hL)
      ((whiskeringLeft _ _ _).mapIso (pairedRestrictionReverseDerivedIso A B C D K F G).symm)

/-- 任意の三つのdg関手に沿う、既存の全導来合成間の比較自然変換。 -/
def simultaneousRestrictionDerivedComparison :
    simultaneousRestrictionDerivedSource A B D C K E L F G H hL ⟶
      endpointRestrictionDerivedTarget A B D C E L F H hE :=
  (simultaneousRestrictionSourceIso A B D C K E L F G H hL).hom ≫
    whiskerRight
      (whiskerLeft (derivedBimoduleRestriction A C L C E (DGFunctor.id C) H)
        (derivedMiddleRestrictionNatTrans A D C K L G hL))
      ((whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))) ≫
    (derivedBimoduleComposeEndpointRestrictionIso A B D C E L F H hE hL).hom

/-- 中間関手だけが準同値なら、三圏を同時制限した比較は両変数で自然な同型。 -/
def derivedBimoduleComposeRestrictionIso (hG : QuasiEquivalence G) :
    simultaneousRestrictionDerivedSource A B D C K E L F G H hL ≅
      endpointRestrictionDerivedTarget A B D C E L F H hE :=
  simultaneousRestrictionSourceIso A B D C K E L F G H hL ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (derivedBimoduleRestriction A C L C E (DGFunctor.id C) H)
        (derivedMiddleRestrictionIso A D C K L G hG hL))
      ((whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))) ≪≫
    derivedBimoduleComposeEndpointRestrictionIso A B D C E L F H hE hL

lemma derivedBimoduleComposeRestrictionIso_hom (hG : QuasiEquivalence G) :
    (derivedBimoduleComposeRestrictionIso A B D C K E L F G H hE hL hG).hom =
      simultaneousRestrictionDerivedComparison A B D C K E L F G H hE hL := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleSimultaneousRestriction
