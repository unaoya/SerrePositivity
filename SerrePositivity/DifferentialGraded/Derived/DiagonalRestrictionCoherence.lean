module
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestrictionCoherence
public import SerrePositivity.DifferentialGraded.Derived.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Derived.PairedRestrictionCoherence

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
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
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
