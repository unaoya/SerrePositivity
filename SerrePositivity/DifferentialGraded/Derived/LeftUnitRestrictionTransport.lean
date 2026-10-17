module
public import SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionSource

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
