module

public import SerrePositivity.DifferentialGraded.Tensor.LeftUnitRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.ModelIndependence
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution
public import SerrePositivity.DifferentialGraded.Derived.Bimodule
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.IteratedModels
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Derived.Functor

/-!
# Derived.LeftUnit

## 概要
8 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## RightUnitRestriction（旧 SerrePositivity/DifferentialGraded/Derived/RightUnitRestriction.lean） -/

/-! # 対角の解像度で計算する導来中間比較と右単位子の整合性

## 概要
対角の解像度で計算する導来中間比較と右単位子の整合性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightUnitRestriction
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)
  (hD : localHomKFlat A D) (hF : HomQuasiIso F)

local notation "QF" => Functor.obj (rightKFlatLeftRestriction A C C D F)
  (rightKFlatDiagonal A C)
local notation "qF" => Bimodule.diagonalRestrictionMap A D C F
local notation "hqF" => Iff.mpr (Bimodule.diagonalRestrictionMap_quasiIso_iff A D C F) hF
local notation "LP" P => Functor.obj
  (BimoduleCategory.middleLeftRestrictionFunctor A B C D F) P

/-- Hom準同型性により対角を制限後の解像度に選ぶと、増大と計算同型が打ち消し合う。 -/
lemma rightUnitRestriction_source_computation (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B D D hD).map
        ((bimoduleToDerived A D D).map qF)).app ((bimoduleToDerived A B D).obj (LP P)) ≫
      (middleRestrictionSourceComputation A B C D D F hD P (QF).obj
        (rightKFlatDiagonal A D) qF hqF).hom =
    (derivedBimoduleComposeKFlatValueIso A B D D hD (rightKFlatDiagonal A D) (LP P)).hom := by
  have h := congrArg (fun k => k.app ((bimoduleToDerived A B D).obj (LP P)))
    (derivedBimoduleComposeResolutionComputation_fac A B D D hD _
      (rightKFlatDiagonal A D) qF hqF)
  change _ ≫ (_ ≫ 𝟙 _) = _
  rw [Category.comp_id]
  exact h

/-- 実際の導来中間比較を対角解像度で計算した右単位square。Cの局所Hom条件は不要。 -/
lemma derivedRightUnitRestriction_model (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B D D hD).map
        ((bimoduleToDerived A D D).map qF)).app ((bimoduleToDerived A B D).obj (LP P)) ≫
      derivedMiddleRestrictionComparison A B C D D F hD P QF
        (rightKFlatDiagonal A D) qF hqF ≫
      (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (bimoduleToDerived A B D).map
        (composeLeftRestrictionIso A B C C D F P (rightKFlatDiagonal A C).obj).hom ≫
      (bimoduleToDerived A B D).map
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map
          (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom) =
    (derivedBimoduleRightUnitIso A B D hD).hom.app ((bimoduleToDerived A B D).obj (LP P)) := by
  unfold derivedMiddleRestrictionComparison
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, rightUnitRestriction_source_computation A B C D F hD hF P]
  rw [derivedBimoduleRightUnitIso_base_app]
  rw [← (bimoduleToDerived A B D).map_comp,
    ← (bimoduleToDerived A B D).map_comp]
  have h := rightUnitRestriction A B C D F P
  rw [← Category.assoc (composeMap A B D D (𝟙 (LP P)) qF)] at h
  change middleRestrictionResolvedMap A B C D D F P (QF).obj (rightKFlatDiagonal A D).obj qF ≫
      (composeLeftRestrictionIso A B C C D F P (rightKFlatDiagonal A C).obj).hom ≫
      (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map
        (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom =
    (rightBimoduleUnitIso A B D (BimoduleCategory.underlying A B D (LP P))).hom at h
  rw [h]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightUnitRestriction

/-! ## RightUnitRestrictionFull（旧 SerrePositivity/DifferentialGraded/Derived/RightUnitRestrictionFull.lean） -/

/-! # 全導来前因子上の中間制限比較と右単位子

## 概要
全導来前因子上の中間制限比較と右単位子。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightUnitRestrictionFull
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)
  (hD : localHomKFlat A D)

local notation "QF" => Functor.obj (rightKFlatLeftRestriction A C C D F)
  (rightKFlatDiagonal A C)
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "HD" => derivedBimoduleComposeFunctor A B D D hD
local notation "ID" => Functor.obj (bimoduleToDerived A D D)
  (BimoduleCategory.of A D D (Bimodule.diagonal A D))
local notation "LP" P => Functor.obj
  (BimoduleCategory.middleLeftRestrictionFunctor A B C D F) P

/-- 対角のHom写像と既存の右側導来制限表示を通した、導来合成間の自然変換。 -/
def rightUnitRestrictionMiddleMap :
    L ⋙ (HD).obj ID ⟶
      (middleRestrictionDerivedSource A B C D D F hD).obj
        ((bimoduleToDerived A C D).obj (QF).obj) :=
  whiskerLeft L ((HD).map
    ((bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D C F) ≫
      (middleRightRestrictionDerivedIso A C D F D).hom.app (QF).obj))

/-- 実際の全導来中間比較、外側左制限比較、右単位子を続けた経路。 -/
def rightUnitRestrictionDerivedComparison : L ⋙ (HD).obj ID ⟶ L :=
  rightUnitRestrictionMiddleMap A B C D F hD ≫
    (derivedMiddleRestrictionNatTrans A B C D D F hD).app
      ((bimoduleToDerived A C D).obj (QF).obj) ≫
    (derivedBimoduleComposeKFlatIso A B C D hD QF).hom ≫
    (derivedComposeWithLeftRestrictionIso A B C C D F (rightKFlatDiagonal A C)).hom ≫
    whiskerRight (derivedRightUnitIso A B C).hom L

/-- 中間比較のsource表示同型を、前因子・後因子の既存表示に分けた計算式。 -/
lemma rightUnitRestriction_source_identification (P : BimoduleCategory A B C) :
    (middleDerivedSourceFamilyIdentification A B C D D F hD QF).hom.app P =
      ((HD).obj ((bimoduleToDerived A D D).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A C D D F).obj (QF).obj))).map
          ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      ((HD).map ((middleRightRestrictionDerivedIso A C D F D).hom.app (QF).obj)).app
        ((L).obj ((bimoduleToDerived A B C).obj P)) := rfl

/-- sourceの制限表示を前合成すると、全導来中間比較の既存モデル計算へ戻る。 -/
lemma rightUnitRestrictionMiddleMap_base_fac (P : BimoduleCategory A B C) :
    ((HD).obj ID).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      (rightUnitRestrictionMiddleMap A B C D F hD).app ((bimoduleToDerived A B C).obj P) ≫
      ((derivedMiddleRestrictionNatTrans A B C D D F hD).app
        ((bimoduleToDerived A C D).obj (QF).obj)).app ((bimoduleToDerived A B C).obj P) =
    ((HD).map ((bimoduleToDerived A D D).map
        (Bimodule.diagonalRestrictionMap A D C F))).app
        ((bimoduleToDerived A B D).obj (LP P)) ≫
      derivedMiddleRestrictionCanonicalComparison A B C D D F hD P QF := by
  let a := (middleLeftRestrictionDerivedIso A B C D F).hom.app P
  let b := (HD).map ((bimoduleToDerived A D D).map
    (Bimodule.diagonalRestrictionMap A D C F))
  let c := (HD).map ((middleRightRestrictionDerivedIso A C D F D).hom.app (QF).obj)
  have hn := b.naturality a
  have hc : ((HD).obj ID).map a ≫
      (rightUnitRestrictionMiddleMap A B C D F hD).app ((bimoduleToDerived A B C).obj P) =
    b.app ((bimoduleToDerived A B D).obj (LP P)) ≫
      (middleDerivedSourceFamilyIdentification A B C D D F hD QF).hom.app P := by
    rw [rightUnitRestriction_source_identification]
    change ((HD).obj ID).map a ≫ ((HD).map
      ((bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D C F) ≫
        (middleRightRestrictionDerivedIso A C D F D).hom.app (QF).obj)).app
      ((L).obj ((bimoduleToDerived A B C).obj P)) = _
    rw [(HD).map_comp, NatTrans.comp_app]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ c.app ((L).obj ((bimoduleToDerived A B C).obj P))) hn).trans
        (Category.assoc _ _ _))
  rw [← Category.assoc, hc, Category.assoc,
    derivedMiddleRestrictionNatTrans_base_fac]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightUnitRestrictionFull

/-! ## RightUnitRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Derived/RightUnitRestrictionCoherence.lean） -/

/-! # 既存の全導来中間比較と右単位子の可換図式

## 概要
既存の全導来中間比較と右単位子の可換図式。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightUnitRestrictionCoherence
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)
  (hD : localHomKFlat A D)

local notation "QF" => Functor.obj (rightKFlatLeftRestriction A C C D F)
  (rightKFlatDiagonal A C)
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "HD" => derivedBimoduleComposeFunctor A B D D hD
local notation "ID" => Functor.obj (bimoduleToDerived A D D)
  (BimoduleCategory.of A D D (Bimodule.diagonal A D))
local notation "LP" P => Functor.obj
  (BimoduleCategory.middleLeftRestrictionFunctor A B C D F) P

/-- 既存の外側左制限比較と右単位子の経路を、通常のbimodule射に計算する。 -/
lemma rightUnitRestriction_target_calculation (P : BimoduleCategory A B C) :
    (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C C D F (rightKFlatDiagonal A C)).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (L).map ((derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P)) =
    (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (bimoduleToDerived A B D).map
        (composeLeftRestrictionIso A B C C D F P (rightKFlatDiagonal A C).obj).hom ≫
      (bimoduleToDerived A B D).map
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map
          (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom) ≫
      (middleLeftRestrictionDerivedIso A B C D F).hom.app P := by
  rw [derivedComposeWithLeftRestrictionIso_hom_app_calc, derivedRightUnitIso_base_app]
  change _ ≫ (𝟙 _ ≫ _ ≫ _ ≫ (L).map (𝟙 _)) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  let f : (composeWith A B C C (rightKFlatDiagonal A C).obj).obj P ⟶ P :=
    (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom
  have hn := (middleLeftRestrictionDerivedIso A B C D F).hom.naturality f
  change (bimoduleToDerived A B D).map
      ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map f) ≫
      (middleLeftRestrictionDerivedIso A B C D F).hom.app P =
    (middleLeftRestrictionDerivedIso A B C D F).hom.app
      ((composeWith A B C C (rightKFlatDiagonal A C).obj).obj P) ≫
      (L).map ((bimoduleToDerived A B C).map f) at hn
  simpa only [Category.assoc] using
    congrArg (fun k => (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (bimoduleToDerived A B D).map
        (composeLeftRestrictionIso A B C C D F P (rightKFlatDiagonal A C).obj).hom ≫ k) hn.symm

/-- 右単位squareの全導来比較を、元の前因子上のモデル計算へ帰着する。 -/
lemma rightUnitRestrictionDerivedComparison_base_fac (hF : HomQuasiIso F)
    (P : BimoduleCategory A B C) :
    ((HD).obj ID).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      (rightUnitRestrictionDerivedComparison A B C D F hD).app
        ((bimoduleToDerived A B C).obj P) =
    (derivedBimoduleRightUnitIso A B D hD).hom.app ((bimoduleToDerived A B D).obj (LP P)) ≫
      (middleLeftRestrictionDerivedIso A B C D F).hom.app P := by
  have hm := rightUnitRestrictionMiddleMap_base_fac A B C D F hD P
  have hs := derivedMiddleRestrictionComparison_kFlat_eq_canonical A B C D D F hD QF
    (rightKFlatDiagonal A D) (Bimodule.diagonalRestrictionMap A D C F)
    ((Bimodule.diagonalRestrictionMap_quasiIso_iff A D C F).2 hF) P
  have ht := rightUnitRestriction_target_calculation A B C D F hD P
  have hu := derivedRightUnitRestriction_model A B C D F hD hF P
  simp only [rightUnitRestrictionDerivedComparison, NatTrans.comp_app, whiskerRight_app]
  have h := congrArg (fun k => k ≫
    (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C C D F (rightKFlatDiagonal A C)).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (L).map ((derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P))) hm
  simp only [Category.assoc] at h
  refine h.trans ?_
  have hs' := congrArg (fun k => ((HD).map ((bimoduleToDerived A D D).map
      (Bimodule.diagonalRestrictionMap A D C F))).app
        ((bimoduleToDerived A B D).obj (LP P)) ≫ k ≫
      (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C C D F (rightKFlatDiagonal A C)).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (L).map ((derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P))) hs.symm
  refine hs'.trans ?_
  have ht' := congrArg (fun k => ((HD).map ((bimoduleToDerived A D D).map
      (Bimodule.diagonalRestrictionMap A D C F))).app
        ((bimoduleToDerived A B D).obj (LP P)) ≫
      derivedMiddleRestrictionComparison A B C D D F hD P QF (rightKFlatDiagonal A D)
        (Bimodule.diagonalRestrictionMap A D C F)
        ((Bimodule.diagonalRestrictionMap_quasiIso_iff A D C F).2 hF) ≫ k) ht
  refine ht'.trans ?_
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ (middleLeftRestrictionDerivedIso A B C D F).hom.app P) hu

/-- 任意の導来前因子で、対角・中間・外側比較の経路は制限後の右単位子と一致する。 -/
lemma rightUnitRestrictionDerivedComparison_eq (hF : HomQuasiIso F) :
    rightUnitRestrictionDerivedComparison A B C D F hD =
      whiskerLeft L (derivedBimoduleRightUnitIso A B D hD).hom := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  apply (Iso.cancel_iso_hom_left
    (((HD).obj ID).mapIso ((middleLeftRestrictionDerivedIso A B C D F).app P)) _ _).1
  change ((HD).obj ID).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫ _ =
    ((HD).obj ID).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      (derivedBimoduleRightUnitIso A B D hD).hom.app
        ((L).obj ((bimoduleToDerived A B C).obj P))
  rw [rightUnitRestrictionDerivedComparison_base_fac A B C D F hD hF P]
  exact ((derivedBimoduleRightUnitIso A B D hD).hom.naturality
    ((middleLeftRestrictionDerivedIso A B C D F).hom.app P)).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightUnitRestrictionCoherence

/-! ## LeftUnitRestrictionFull（旧 SerrePositivity/DifferentialGraded/Derived/LeftUnitRestrictionFull.lean） -/

/-! # 対角・外側右・中間比較を続ける全導来左単位経路

## 概要
対角・外側右・中間比較を続ける全導来左単位経路。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftUnitRestrictionFull
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)

local notation "DB" => BimoduleCategory.of A B B (Bimodule.diagonal A B)
local notation "DD" => BimoduleCategory.of A D D (Bimodule.diagonal A D)
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F) DB
local notation "RR" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)

/-- 直接の対角比較を、外側右制限の既存導来表示へ送る。 -/
def leftUnitRestrictionDerivedDiagonalMap :
    (bimoduleToDerived A D D).obj DD ⟶
      (derivedBimoduleRestriction A D D B D F (DGFunctor.id D)).obj
        ((bimoduleToDerived A B D).obj LD) :=
  (bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D B F) ≫
    (middleRightRestrictionDerivedIso A B D F D).hom.app LD

/-- 既存の全導来中間比較・外側右制限比較・左単位子を続けた自然変換。 -/
def leftUnitRestrictionDerivedComparison (hC : localHomKFlat A C) :
    RR ⋙ derivedBimoduleLeftUnitFunctor A D C hC ⟶ RR :=
  whiskerLeft (RR ⋙ derivedBimoduleComposeFunctor A D D C hC)
      ((CategoryTheory.evaluation _ _).map (leftUnitRestrictionDerivedDiagonalMap A B D F)) ≫
    whiskerRight
      (whiskerLeft RR (derivedBimoduleComposeRightRestrictionIso A B D D C F hC).hom)
      ((CategoryTheory.evaluation _ _).obj ((bimoduleToDerived A B D).obj LD)) ≫
    whiskerLeft (RR ⋙ derivedBimoduleComposeFunctor A B D C hC ⋙
        (whiskeringRight _ _ _).obj RR)
      ((CategoryTheory.evaluation _ _).map
        ((middleLeftRestrictionDerivedIso A B B D F).hom.app DB)) ≫
    whiskerRight
      (whiskerRight (derivedMiddleRestrictionNatTrans A B B D C F hC)
        ((CategoryTheory.evaluation _ _).obj ((bimoduleToDerived A B B).obj DB))) RR ≫
    whiskerRight (derivedBimoduleLeftUnitIso A B C hC).hom RR

/-- 左単位経路の各成分は、既存比較の実際の成分を順に続けた射である。 -/
lemma leftUnitRestrictionDerivedComparison_app (hC : localHomKFlat A C)
    (Q : DerivedBimoduleCategory A B C) :
    (leftUnitRestrictionDerivedComparison A B D C F hC).app Q =
      ((derivedBimoduleComposeFunctor A D D C hC).obj ((RR).obj Q)).map
        (leftUnitRestrictionDerivedDiagonalMap A B D F) ≫
      ((derivedBimoduleComposeRightRestrictionIso A B D D C F hC).hom.app ((RR).obj Q)).app
        ((bimoduleToDerived A B D).obj LD) ≫
      (RR).map (((derivedBimoduleComposeFunctor A B D C hC).obj ((RR).obj Q)).map
        ((middleLeftRestrictionDerivedIso A B B D F).hom.app DB)) ≫
      (RR).map (((derivedMiddleRestrictionNatTrans A B B D C F hC).app Q).app
        ((bimoduleToDerived A B B).obj DB)) ≫
      (RR).map ((derivedBimoduleLeftUnitIso A B C hC).hom.app Q) := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end LeftUnitRestrictionFull

/-! ## LeftUnitRestrictionNormalization（旧 SerrePositivity/DifferentialGraded/Derived/LeftUnitRestrictionNormalization.lean） -/

/-! # 対角を代入した全導来左単位経路のモデル正規化

## 概要
対角を代入した全導来左単位経路のモデル正規化。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftUnitRestrictionNormalization
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [dgB : DGCategory A B] [smallB : Small.{u} B]
  (D : Type w) [dgD : DGCategory A D] [smallD : Small.{u} D]
  (C : Type z) [dgC : DGCategory A C] [smallC : Small.{u} C] (F : DGFunctor A D B)
  (hC : localHomKFlat A C) (Q : RightKFlatBimoduleCategory A B C)
  (R : RightKFlatBimoduleCategory A D C)

local notation "DB" => BimoduleCategory.of A B B (Bimodule.diagonal A B)
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F) DB
local notation "RR" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)

/-- 一般のモデルprefixを対角の左制限に特殊化した、既存比較の射。 -/
def leftUnitRestrictedModelPrefix := fun q hq =>
  restrictedMiddleModelPrefix A B B D C F D F hC DB Q R q hq

/-- 指定モデル上で、対角射と外側・中間比較に左単位子を続けた実際の経路。 -/
def leftUnitRestrictionModelPath := fun q hq =>
  (derivedComposeWith A D D C R.obj R.property).map
      ((bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D B F)) ≫
    leftUnitRestrictedModelPrefix A B D C F hC Q R q hq ≫
    (RR).map
      ((middleDerivedSourceFamilyIdentification A B B D C F hC Q).hom.app DB ≫
        ((derivedMiddleRestrictionNatTrans A B B D C F hC).app
          ((bimoduleToDerived A B C).obj Q.obj)).app ((bimoduleToDerived A B B).obj DB) ≫
        (derivedBimoduleComposeKFlatValueIso A B B C hC Q DB).hom) ≫
    (RR).map ((bimoduleToDerived A B C).map ((leftUnitNatIso A B C).hom.app Q.obj))

private lemma paste_unit_square {V W : Type*} [Category* V] [Category* W] (H : V ⥤ W)
    {a b c d e : W} {x y : V} (p : a ⟶ b) (m : b ⟶ H.obj x)
    (f : x ⟶ y) (r : b ⟶ c) (s : c ⟶ d) (u : d ⟶ H.obj x)
    (v : d ⟶ e) (w : e ⟶ H.obj y) (t : a ⟶ e)
    (h₁ : m = r ≫ s ≫ u) (h₂ : u ≫ H.map f = v ≫ w) (h₃ : p ≫ r ≫ s ≫ v = t) :
    p ≫ m ≫ H.map f = t ≫ w := by
  rw [h₁]
  simp only [Category.assoc]
  rw [h₂]
  exact (by simpa only [Category.assoc] using congrArg (fun k => k ≫ w) h₃)

/-- 対角での組合せのモデル計算は、Rの左単位子に増大射を続けた射に一致する。 -/
lemma leftUnitRestrictionModelPath_eq (q : _) (hq : _) :
    leftUnitRestrictionModelPath A B D C F hC Q R q hq =
      (bimoduleToDerived A D C).map ((leftUnitNatIso A D C).hom.app R.obj) ≫
      (bimoduleToDerived A D C).map q ≫
      (middleRightRestrictionDerivedIso A B D F C).hom.app Q.obj := by
  let U := (composeWith A B B C Q.obj).obj DB
  let f : U ⟶ Q.obj := (leftUnitNatIso A B C).hom.app Q.obj
  have hm := derivedBimoduleRestriction_model_calculation A B B D C F D F hC DB Q R q hq
  have hn := (middleRightRestrictionDerivedIso A B D F C).hom.naturality f
  have hu := leftUnitRestriction_localized_augmentation A B D C F Q.obj R.obj q
  unfold leftUnitRestrictionModelPath
  rw [derivedComposeWith_map_base]
  have result := paste_unit_square (RR)
    ((bimoduleToDerived A D C).map
      (composeMap A D D C (Bimodule.diagonalRestrictionMap A D B F) (𝟙 R.obj)))
    _ ((bimoduleToDerived A B C).map f) _ _ _ _ _ _ hm hn.symm hu
  convert result using 1 <;>
    first | rfl | simp only [leftUnitRestrictedModelPrefix, f, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end LeftUnitRestrictionNormalization

/-! ## LeftUnitRestrictionSource（旧 SerrePositivity/DifferentialGraded/Derived/LeftUnitRestrictionSource.lean） -/

/-! # 指定解像度から全導来左単位子のsourceへの表示同型

## 概要
指定解像度から全導来左単位子のsourceへの表示同型。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftUnitRestrictionSource
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)
  (hC : localHomKFlat A C) (Q : RightKFlatBimoduleCategory A B C)
  (R : RightKFlatBimoduleCategory A D C)

local notation "DD" => BimoduleCategory.of A D D (Bimodule.diagonal A D)
local notation "RQ" => Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A B D C F) Q.obj
local notation "RR" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)

/-- 指定モデルでの合成を、制限表示を通して全導来左単位子のsourceへ送る。 -/
def leftUnitRestrictionModelSourceIso := fun q hq =>
  ((derivedBimoduleComposeResolutionComputation A D D C hC RQ R q hq).app
      ((bimoduleToDerived A D D).obj DD)).symm ≪≫
    (derivedBimoduleLeftUnitFunctor A D C hC).mapIso
      ((middleRightRestrictionDerivedIso A B D F C).app Q.obj)

private lemma paste_unit_naturality {V : Type*} [Category* V]
    {a b c d e : V} (s : a ≅ b) (p : b ⟶ c) (u : c ⟶ d)
    (v : b ⟶ e) (w : e ⟶ d) (t : a ⟶ e)
    (hn : p ≫ u = v ≫ w) (hv : v = s.inv ≫ t) :
    s.hom ≫ p ≫ u = t ≫ w := by
  rw [hn, hv]
  simp only [← Category.assoc, s.hom_inv_id, Category.id_comp]

/-- 既存の左単位子は、source表示の後でRの左単位子・増大射・制限表示に計算される。 -/
lemma leftUnitRestrictionModelSourceIso_leftUnit (q : _) (hq : _) :
    (leftUnitRestrictionModelSourceIso A B D C F hC Q R q hq).hom ≫
      (derivedBimoduleLeftUnitIso A D C hC).hom.app
        ((RR).obj ((bimoduleToDerived A B C).obj Q.obj)) =
    (bimoduleToDerived A D C).map ((leftUnitNatIso A D C).hom.app R.obj) ≫
      (bimoduleToDerived A D C).map q ≫
      (middleRightRestrictionDerivedIso A B D F C).hom.app Q.obj := by
  let s := (derivedBimoduleComposeResolutionComputation A D D C hC RQ R q hq).app
    ((bimoduleToDerived A D D).obj DD)
  have hn := (derivedBimoduleLeftUnitIso A D C hC).hom.naturality
    ((middleRightRestrictionDerivedIso A B D F C).hom.app Q.obj)
  have hv := derivedBimoduleLeftUnitIso_resolution_app A D C hC RQ R q hq
  have result := paste_unit_naturality s.symm _ _ _ _ _ hn hv
  convert result using 1 <;>
    first
    | rfl
    | (simp only [leftUnitRestrictionModelSourceIso, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, s, Category.assoc]; try rfl)

/-- モデル経路は、同じsource表示を通した既存の全導来左単位子と一致する。 -/
lemma leftUnitRestrictionModelPath_eq_sourceLeftUnit (q : _) (hq : _) :
    leftUnitRestrictionModelPath A B D C F hC Q R q hq =
    (leftUnitRestrictionModelSourceIso A B D C F hC Q R q hq).hom ≫
      (derivedBimoduleLeftUnitIso A D C hC).hom.app
        ((RR).obj ((bimoduleToDerived A B C).obj Q.obj)) := by
  rw [leftUnitRestrictionModelPath_eq, leftUnitRestrictionModelSourceIso_leftUnit]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end LeftUnitRestrictionSource

/-! ## LeftUnitRestrictionTransport（旧 SerrePositivity/DifferentialGraded/Derived/LeftUnitRestrictionTransport.lean） -/

/-! # 全導来左単位比較を指定K-flatモデル経路へ輸送する

## 概要
全導来左単位比較を指定K-flatモデル経路へ輸送する。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftUnitRestrictionTransport
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)
  (hC : localHomKFlat A C) (Q : RightKFlatBimoduleCategory A B C)
  (R : RightKFlatBimoduleCategory A D C)

local notation "DB" => BimoduleCategory.of A B B (Bimodule.diagonal A B)
local notation "DD" => BimoduleCategory.of A D D (Bimodule.diagonal A D)
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F) DB
local notation "RQ" => Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A B D C F) Q.obj
local notation "RR" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "HD" => derivedBimoduleComposeFunctor A D D C hC

private lemma presentation_naturality {V W T : Type*}
    [Category* V] [Category* W] [Category* T] (H : T ⥤ V ⥤ W)
    {x y : T} {M : V ⥤ W} (c : H.obj x ≅ M) (e : x ⟶ y)
    {a b : V} (f : a ⟶ b) :
    c.inv.app a ≫ (H.map e).app a ≫ (H.obj y).map f =
      M.map f ≫ c.inv.app b ≫ (H.map e).app b := by
  have h := (c.inv ≫ H.map e).naturality f
  simpa only [NatTrans.comp_app, Category.assoc] using h.symm

/-- 対角射に関する計算同型と後因子制限表示の自然性。 -/
lemma leftUnitRestrictionModelSourceIso_diagonal (q : _) (hq : _) :
    (leftUnitRestrictionModelSourceIso A B D C F hC Q R q hq).hom ≫
      ((HD).obj ((RR).obj ((bimoduleToDerived A B C).obj Q.obj))).map
        ((bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D B F)) =
    (derivedComposeWith A D D C R.obj R.property).map
        ((bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D B F)) ≫
      (derivedBimoduleComposeResolutionComputation A D D C hC RQ R q hq).inv.app
        ((bimoduleToDerived A D D).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A B D D F).obj LD)) ≫
      ((HD).map ((middleRightRestrictionDerivedIso A B D F C).hom.app Q.obj)).app
        ((bimoduleToDerived A D D).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A B D D F).obj LD)) := by
  have h := presentation_naturality (HD)
    (derivedBimoduleComposeResolutionComputation A D D C hC RQ R q hq)
    ((middleRightRestrictionDerivedIso A B D F C).hom.app Q.obj)
    ((bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D B F))
  convert h using 1 <;>
    first
    | rfl
    | (simp only [leftUnitRestrictionModelSourceIso, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, Category.assoc]; try rfl)

private lemma paste_prefix {V : Type*} [Category* V]
    {a b c d e f h i j : V}
    (p : a ⟶ b) (δ : b ⟶ c) (r : c ⟶ d) (s : d ⟶ e) (t : e ⟶ f)
    (δ₀ : a ⟶ h) (c₀ : h ⟶ i) (e₀ : i ⟶ c) (pre : h ⟶ j) (fam : j ⟶ f)
    (hδ : p ≫ δ = δ₀ ≫ c₀ ≫ e₀)
    (hs : c₀ ≫ e₀ ≫ r ≫ s ≫ t = pre ≫ fam) :
    p ≫ δ ≫ r ≫ s ≫ t = δ₀ ≫ pre ≫ fam := by
  rw [← Category.assoc p δ, hδ]
  simpa only [Category.assoc] using congrArg (fun k => δ₀ ≫ k) hs

/-- 全導来左単位経路の、対角射・外側比較・前因子表示までの部分。 -/
def leftUnitRestrictionDerivedPrefix :=
  ((HD).obj ((RR).obj ((bimoduleToDerived A B C).obj Q.obj))).map
      (leftUnitRestrictionDerivedDiagonalMap A B D F) ≫
    ((derivedBimoduleComposeRightRestrictionIso A B D D C F hC).hom.app
      ((RR).obj ((bimoduleToDerived A B C).obj Q.obj))).app
        ((bimoduleToDerived A B D).obj LD) ≫
    (RR).map (((derivedBimoduleComposeFunctor A B D C hC).obj
      ((RR).obj ((bimoduleToDerived A B C).obj Q.obj))).map
        ((middleLeftRestrictionDerivedIso A B B D F).hom.app DB))

/-- 対角射とsource正規化を接続した、全導来prefixの指定モデル計算。 -/
lemma leftUnitRestrictionDerivedPrefix_model (q : _) (hq : _) :
    (leftUnitRestrictionModelSourceIso A B D C F hC Q R q hq).hom ≫
      leftUnitRestrictionDerivedPrefix A B D C F hC Q =
    (derivedComposeWith A D D C R.obj R.property).map
        ((bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D B F)) ≫
      leftUnitRestrictedModelPrefix A B D C F hC Q R q hq ≫
      (RR).map ((middleDerivedSourceFamilyIdentification A B B D C F hC Q).hom.app DB) := by
  have hδ := leftUnitRestrictionModelSourceIso_diagonal A B D C F hC Q R q hq
  have hs := restrictedMiddleSourcePrefix_model A B B D C F D F hC DB Q R q hq
  simp only [restrictedMiddleSourcePrefix] at hs
  have result := paste_prefix _ _ _ _ _ _ _ _ _ _ hδ hs
  unfold leftUnitRestrictionDerivedPrefix leftUnitRestrictedModelPrefix
  convert result using 1
  simp only [leftUnitRestrictionDerivedDiagonalMap,
    CategoryTheory.Functor.map_comp, Category.assoc]

/-- 実際の全導来比較は、任意の指定モデルのsource表示を通すとモデル経路に一致する。 -/
lemma leftUnitRestrictionDerivedComparison_model (q : _) (hq : _) :
    (leftUnitRestrictionModelSourceIso A B D C F hC Q R q hq).hom ≫
      (leftUnitRestrictionDerivedComparison A B D C F hC).app
        ((bimoduleToDerived A B C).obj Q.obj) =
    leftUnitRestrictionModelPath A B D C F hC Q R q hq := by
  have hp := leftUnitRestrictionDerivedPrefix_model A B D C F hC Q R q hq
  have hu := congrArg (RR).map (derivedBimoduleLeftUnitIso_kFlat_base_app A B C hC Q)
  simp only [CategoryTheory.Functor.map_comp] at hu
  have h := congrArg (fun k => k ≫
    (RR).map (((derivedMiddleRestrictionNatTrans A B B D C F hC).app
      ((bimoduleToDerived A B C).obj Q.obj)).app ((bimoduleToDerived A B B).obj DB)) ≫
    (RR).map ((derivedBimoduleLeftUnitIso A B C hC).hom.app
      ((bimoduleToDerived A B C).obj Q.obj))) hp
  rw [hu] at h
  have hraw : (leftUnitNatIso A B C).hom.app Q.obj =
      (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C Q.obj)).hom := rfl
  convert h using 1 <;>
    simp only [leftUnitRestrictionDerivedComparison_app,
      leftUnitRestrictionDerivedPrefix, leftUnitRestrictionModelPath,
      CategoryTheory.Functor.map_comp, hu, hraw, rightKFlatDiagonal, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end LeftUnitRestrictionTransport

/-! ## LeftUnitRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Derived/LeftUnitRestrictionCoherence.lean） -/

/-! # 全導来左単位経路と制限後の既存左単位子の一致

## 概要
全導来左単位経路と制限後の既存左単位子の一致。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftUnitRestrictionCoherence
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)
  (hC : localHomKFlat A C)

local notation "RR" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)

/-- 任意の指定解像度のsource同型を打ち消した、右K-flat後因子上の左単位square。 -/
lemma leftUnitRestrictionDerivedComparison_kFlat
    (Q : RightKFlatBimoduleCategory A B C) (R : RightKFlatBimoduleCategory A D C)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D C q) :
    (leftUnitRestrictionDerivedComparison A B D C F hC).app
        ((bimoduleToDerived A B C).obj Q.obj) =
      (derivedBimoduleLeftUnitIso A D C hC).hom.app
        ((RR).obj ((bimoduleToDerived A B C).obj Q.obj)) := by
  apply (Iso.cancel_iso_hom_left
    (leftUnitRestrictionModelSourceIso A B D C F hC Q R q hq) _ _).1
  exact (leftUnitRestrictionDerivedComparison_model A B D C F hC Q R q hq).trans
    (leftUnitRestrictionModelPath_eq_sourceLeftUnit A B D C F hC Q R q hq)

/-- 任意のdg関手に沿い、全導来外側・中間比較の左単位経路は既存左単位子と一致する。 -/
lemma leftUnitRestrictionDerivedComparison_eq :
    leftUnitRestrictionDerivedComparison A B D C F hC =
      whiskerLeft RR (derivedBimoduleLeftUnitIso A D C hC).hom := by
  apply rightKFlatDerivedNatTrans_ext A B C hC
  intro Q
  let M := (BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj Q.obj
  let R := rightKFlatResolutionObj A D C hC M
  exact leftUnitRestrictionDerivedComparison_kFlat A B D C F hC Q R
    (bimoduleCanonicalSemifreeResolution A D C M).π
    (bimoduleCanonicalSemifreeResolution A D C M).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end LeftUnitRestrictionCoherence
