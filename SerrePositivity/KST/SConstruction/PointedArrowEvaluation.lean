module
public import SerrePositivity.KST.SConstruction.PointedExtensionArrowDiagram
public import SerrePositivity.KST.SConstruction.PointedLiftArrowDiagram
public import SerrePositivity.KST.SConstruction.InverseMixedFamilyTransport

/-! # 全入力射上の写像空間図式と選択の評価
概要：混合選択の図式を、元の点つき写像空間の両変数図式へ自然に評価する。
方針：全次数の射影の移送と自然な retraction の評価公式を使う。
規約：頂点だけの等号に弱めず図式の自然変換として構成する。
使われ方：coherent な因子の全選択を元の構造射の写像族へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra Spectra.PointedMapping

/-- 全入力射に対応する点つき写像空間の両側合成の図式。 -/
def pointedMappingArrowDiagram {J : Type v} [Category.{w} J]
    (A L : J ⥤ PointedSimplicialSet.{u}) : AssemblyInputArrow J ⥤ SSet.{u} where
  obj x := (PointedObject.basedHom (A.obj (assemblyArrowSource x))
    (L.obj (assemblyArrowTarget x))).right
  map h := pointedMappingTransport (A.map (assemblyArrowPre h)) (L.map (assemblyArrowPost h))
  map_id x := by
    have ha : A.map (assemblyArrowPre (𝟙 x)) = 𝟙 (A.obj (assemblyArrowSource x)) := A.map_id _
    have hl : L.map (assemblyArrowPost (𝟙 x)) = 𝟙 (L.obj (assemblyArrowTarget x)) := L.map_id _
    rw [ha, hl]
    exact pointedMappingTransport_id _ _
  map_comp h k := by
    have ha : A.map (assemblyArrowPre (h ≫ k)) =
        A.map (assemblyArrowPre k) ≫ A.map (assemblyArrowPre h) :=
      (congrArg A.map (assemblyArrowPre_comp h k)).trans (A.map_comp _ _)
    have hl : L.map (assemblyArrowPost (h ≫ k)) =
        L.map (assemblyArrowPost h) ≫ L.map (assemblyArrowPost k) :=
      (congrArg L.map (assemblyArrowPost_comp h k)).trans (L.map_comp _ _)
    rw [ha, hl]
    exact (pointedMappingTransport_comp _ _ _ _).symm

/-- 延長選択図式から、指定した実際の点つき写像の図式への全次数の評価。 -/
def pointedExtensionArrowEvaluation {J : Type v} [Category.{w} J]
    {R A L : J ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L) :
    pointedExtensionArrowDiagram η θ ⟶ pointedMappingArrowDiagram A L where
  app x := pullback.fst
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app (assemblyArrowSource x)) (L.obj (assemblyArrowTarget x))).right
    (SSet.yonedaEquiv.symm (familyVertex
      (R.map (assemblyArrowHom x) ≫ θ.app (assemblyArrowTarget x))))
  naturality _ _ h :=
    pointedExtensionTransport_projection _ _ _ _ _ _ _
      (η.naturality (assemblyArrowPre h)) (pointedExtensionArrow_restriction θ h)

/-- 自然な retraction を持ち上げの族へ合成する評価は、全入力射に関して自然。 -/
def pointedLiftArrowEvaluation {J : Type v} [Category.{w} J]
    {E B A : J ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B) (q : E ⟶ A) :
    pointedLiftArrowDiagram p ⟶ pointedMappingArrowDiagram B A where
  app x := pullback.fst
    (PointedObject.basedHomMap (B.obj (assemblyArrowSource x))
      (p.app (assemblyArrowTarget x))).right
    (SSet.yonedaEquiv.symm (familyVertex (B.map (assemblyArrowHom x)))) ≫
      (PointedObject.basedHomMap (B.obj (assemblyArrowSource x))
        (q.app (assemblyArrowTarget x))).right
  naturality x y h := by
    have hh := pointedLiftTransport_evaluation
      (p.app (assemblyArrowTarget x)) (B.map (assemblyArrowHom x))
      (p.app (assemblyArrowTarget y)) (B.map (assemblyArrowHom y))
      (B.map (assemblyArrowPre h)) (E.map (assemblyArrowPost h)) (B.map (assemblyArrowPost h))
      (p.naturality (assemblyArrowPost h)) (pointedLiftArrow_base B h)
      (q.app (assemblyArrowTarget x)) (q.app (assemblyArrowTarget y))
      (A.map (assemblyArrowPost h)) (q.naturality (assemblyArrowPost h))
    exact hh.trans (Category.assoc _ _ _).symm

end SerrePositivity.KST.SConstruction
