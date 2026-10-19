module
public import SerrePositivity.KST.SConstruction.AssemblyInputIdentityChoices
public import SerrePositivity.KST.SConstruction.PointedArrowIdentityTransport

/-! # 恒等入力の比較と元の混合選択の両端
概要：全入力射図式の二脚は、元の二つの因子の両端移送を厳密に回収する。
方針：点つき延長・持ち上げの恒等成分の比較を元の K の図式へ適用する。
規約：全てのパラメーターと全次数を保持する。
使われ方：全射列の coherent な二脚を既存の自然性の辺の両端へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 延長側の源の恒等成分の比較後の移送は、元の源からの移送。 -/
lemma kanAssemblyInputIdentityChoicesIso_source {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y) :
    (kanAssemblyInputIdentityChoicesIso r F X).hom ≫ kanAssemblyMixedFromSource r (F.map f) =
      (kanAssemblyInputArrowDiagram r F).map (assemblyArrowFromSource f) :=
  pointedExtensionArrowIdentityIso_source
    (Functor.whiskerLeft F (oneDirectionKanUnitNat r))
    (Functor.whiskerLeft F (kanTargetAssemblyAdjointNat r)) f

/-- 延長側の標的の恒等成分の比較後の移送は、元の標的からの移送。 -/
lemma kanAssemblyInputIdentityChoicesIso_target {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y) :
    (kanAssemblyInputIdentityChoicesIso r F Y).hom ≫ kanAssemblyMixedFromTarget r (F.map f) =
      (kanAssemblyInputArrowDiagram r F).map (assemblyArrowFromTarget f) :=
  pointedExtensionArrowIdentityIso_target
    (Functor.whiskerLeft F (oneDirectionKanUnitNat r))
    (Functor.whiskerLeft F (kanTargetAssemblyAdjointNat r)) f

/-- 逆射側の源の恒等成分の比較後の移送は、元の源からの移送。 -/
lemma oneDirectionInverseInputIdentityChoicesIso_source {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y) :
    (oneDirectionInverseInputIdentityChoicesIso r F X).hom ≫
        oneDirectionInverseMixedFromSource r (F.map f) =
      (oneDirectionInverseInputArrowDiagram r F).map (assemblyArrowFromSource f) :=
  pointedLiftArrowIdentityIso_source
    (Functor.whiskerLeft F (oneDirectionMappingPathProjectionNat r)) f

/-- 逆射側の標的の恒等成分の比較後の移送は、元の標的からの移送。 -/
lemma oneDirectionInverseInputIdentityChoicesIso_target {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y) :
    (oneDirectionInverseInputIdentityChoicesIso r F Y).hom ≫
        oneDirectionInverseMixedFromTarget r (F.map f) =
      (oneDirectionInverseInputArrowDiagram r F).map (assemblyArrowFromTarget f) :=
  pointedLiftArrowIdentityIso_target
    (Functor.whiskerLeft F (oneDirectionMappingPathProjectionNat r)) f

end SerrePositivity.KST.SConstruction
