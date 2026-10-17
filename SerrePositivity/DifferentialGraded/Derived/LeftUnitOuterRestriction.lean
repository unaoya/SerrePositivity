module
public import SerrePositivity.DifferentialGraded.Tensor.OuterUnitRestriction
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionPresentation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionLeftUnitComputation

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
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
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
