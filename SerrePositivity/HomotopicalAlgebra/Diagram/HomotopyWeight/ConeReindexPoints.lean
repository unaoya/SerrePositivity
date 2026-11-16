module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConeReindex
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConePoints

/-!
# 添字移送による元の錐の零単体の保存

概要：Hovey §5.4 の錐の添字移送で元の族とその連結成分を照合する。
方針：右随伴の一意性の単位保存から随伴の Hom 対応を計算する。
規約：元の比較同型を保持し、モデル構造を仮定しない。
使われ方：右 frame の錐と元の通常錐の比較の正規化。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.Functor _root_.CategoryTheory.Functor
open _root_.SerrePositivity.DiagramModel _root_.SerrePositivity.DiagramModel.WeightedCones

private lemma rightAdjointUniq_homEquiv {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (b : F ⊣ H)
    {X : C} {Y : D} (t : F.obj X ⟶ Y) :
    a.homEquiv X Y t ≫ (Adjunction.rightAdjointUniq a b).hom.app Y =
      b.homEquiv X Y t := by
  rw [a.homEquiv_unit, b.homEquiv_unit, Category.assoc,
    (Adjunction.rightAdjointUniq a b).hom.naturality,
    ← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]

variable {J K : Type u} [SmallCategory J] [SmallCategory K] (e : J ≌ K)
  (W : K ⥤ SSet.{u})
/-- 概要：添字移送は元の錐の随伴対応を保つ（Hovey §5.4）。
方針：右随伴の一意性が保つ単位と前合成同値の単位を相殺する。
規約：元の coneSpaceReindexIso と元の図式射を使う。
使われ方：錐の零単体の添字移送の計算。 -/
lemma coneSpaceReindexIso_homEquiv (X : SSet.{u}) (F : K ⥤ SSet.{u})
    (t : (tensorDiagram K W).obj X ⟶ F) :
    (WeightedCones.adjunction J (e.functor ⋙ W)).homEquiv X _
        (whiskerLeft e.functor t) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexIso e W).hom.app F =
      (WeightedCones.adjunction K W).homEquiv X F t := by
  let E := e.symm.congrLeft (E := SSet.{u})
  let a := WeightedCones.adjunction J (e.functor ⋙ W)
  let b := (WeightedCones.adjunction K W).comp E.toAdjunction
  have h := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.rightAdjointUniq_homEquiv a (b.ofNatIsoLeft (Iso.refl _)) (whiskerLeft e.functor t)
  change a.homEquiv X _ (whiskerLeft e.functor t) ≫
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexAuxIso e W).hom.app _ ≫
      (coneSpace K W).map (E.unitIso.inv.app F) = _
  rw [← Category.assoc]
  change (a.homEquiv X _ (whiskerLeft e.functor t) ≫
    (Adjunction.rightAdjointUniq a (b.ofNatIsoLeft (Iso.refl _))).hom.app _) ≫ _ = _
  rw [h, Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  dsimp only [b]
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [← (WeightedCones.adjunction K W).homEquiv_naturality_right]
  congr 1
  change E.toAdjunction.homEquiv _ _ (E.functor.map t) ≫ _ = _
  rw [Adjunction.homEquiv_unit]
  change E.unitIso.hom.app _ ≫ E.inverse.map (E.functor.map t) ≫ _ = _
  have hn := (E.unitIso.hom.naturality t).symm
  change E.unitIso.hom.app _ ≫ E.inverse.map (E.functor.map t) =
    t ≫ E.unitIso.hom.app _ at hn
  rw [← Category.assoc, hn, Category.assoc]
  change t ≫ E.unitIso.hom.app F ≫ E.unitIso.inv.app F = t
  rw [Iso.hom_inv_id_app]
  exact Category.comp_id t

/-- 概要：添字移送は元の重み付き族の零単体を保つ（Hovey §5.4）。
方針：同じ零次テンソル同型の各値の一致を随伴比較へ代入する。
規約：別の比較同型や零単体を選ばない。
使われ方：通常の錐の類を両 frame 間で追跡する。 -/
lemma coneSpaceReindexIso_point {F : K ⥤ SSet.{u}} (s : W ⟶ F) :
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexIso e W).hom.app F).app (Opposite.op (SimplexCategory.mk 0))
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint J (e.functor ⋙ W) (whiskerLeft e.functor s)) = _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint K W s := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint, ← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  have h := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexIso_homEquiv e W _ F ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso K W).hom ≫ s)
  have hz : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso J (e.functor ⋙ W)).hom ≫ whiskerLeft e.functor s =
      whiskerLeft e.functor ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso K W).hom ≫ s) := by
    ext j n x
    rfl
  rw [hz]
  exact h

/-- 概要：添字移送は元の族の連結成分を保つ（Hovey §5.4）。
方針：同じ零単体の計算を π₀ に送る。
規約：実際の coneSpaceReindexIso の誘導写像。
使われ方：右錐の元の通常錐による正規化。 -/
lemma coneSpaceReindexIso_class {F : K ⥤ SSet.{u}} (s : W ⟶ F) :
    SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexIso e W).hom.app F)
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass J (e.functor ⋙ W) (whiskerLeft e.functor s)) = _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K W s := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass, SSet.mapπ₀_mk, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexIso_point]
  rfl

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
