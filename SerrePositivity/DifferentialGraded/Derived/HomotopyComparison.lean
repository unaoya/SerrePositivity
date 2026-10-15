module
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Module.Cylinder
public import Mathlib.CategoryTheory.Localization.Quotient

/-! # 閉零加群圏と K(D) の指定局所化の比較

具体的 dg cylinder が境界を同一視させることを証明し、
Mathlib の商の局所化と局所化の一意性を適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定quasiIsoを反転する任意の関手は加群の境界関係を同一視する。 -/
lemma moduleQuasiIso_equalizes_boundary {E : Type w} [Category.{w'} E]
    (F : ModuleCategory A D ⥤ E) (hF : (moduleQuasiIso A D).IsInvertedBy F)
    {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) : F.map f = F.map g := by
  let P := modulePrecylinder A D M
  let H := moduleCylinderLeftHomotopy A D f g h
  let e : F.obj P.I ≅ F.obj M := @asIso E _ _ _ (F.map P.π)
    (hF _ (modulePrecylinder_π_quasiIso A D M))
  have hi : F.map P.i₀ = F.map P.i₁ := by
    have hs : F.map P.i₀ ≫ e.hom = F.map P.i₁ ≫ e.hom := by
      change F.map P.i₀ ≫ F.map P.π = F.map P.i₁ ≫ F.map P.π
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, P.i₀_π, P.i₁_π]
    have hc := congrArg (fun k => k ≫ e.inv) hs
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using hc
  calc
    F.map f = F.map (P.i₀ ≫ H.h) := congrArg F.map H.h₀.symm
    _ = F.map P.i₀ ≫ F.map H.h := F.map_comp _ _
    _ = F.map P.i₁ ≫ F.map H.h := congrArg (fun k => k ≫ F.map H.h) hi
    _ = F.map g := (F.map_comp _ _).symm.trans (congrArg F.map H.h₁)

lemma moduleBoundaryFactorsThroughLocalization :
    (boundaryRelation A (RightModule A D)).FactorsThroughLocalization (moduleQuasiIso A D) := by
  intro M N f g h
  exact moduleQuasiIso_equalizes_boundary A D (moduleToDerived A D)
    (moduleToDerived_inverts A D) f g h

/-- K(D)を経由した局所化も閉零圏の同じquasiIsoを局所化する。 -/
instance moduleHomotopyCompositeIsLocalization :
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D).IsLocalization (moduleQuasiIso A D) := by
  apply Functor.IsLocalization.mk'
  all_goals
    exact ((moduleBoundaryFactorsThroughLocalization A D).strictUniversalPropertyFixedTarget'
      (W' := moduleHomotopyQuasiIso A D) (moduleHomotopyQuasiIso_inverseImage A D).symm _)

/-- 指定した二つの局所化の同値。 -/
def moduleDerivedHomotopyEquivalence :
    DerivedModuleCategory A D ≌ HomotopyDerivedModuleCategory A D :=
  Localization.uniq (moduleToDerived A D)
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) (moduleQuasiIso A D)

/-- 同値の順方向と二つの局所化関手の可換図式。 -/
def moduleDerivedHomotopyComparisonIso :
    moduleToDerived A D ⋙ (moduleDerivedHomotopyEquivalence A D).functor ≅
      moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D :=
  Localization.compUniqFunctor (moduleToDerived A D)
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) (moduleQuasiIso A D)

/-- 逆方向についても局所化関手の比較を公開する。 -/
def moduleDerivedHomotopyInverseComparisonIso :
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) ⋙
      (moduleDerivedHomotopyEquivalence A D).inverse ≅ moduleToDerived A D :=
  Localization.compUniqInverse (moduleToDerived A D)
    (moduleToHomotopy A D ⋙ moduleHomotopyToDerived A D) (moduleQuasiIso A D)

/-- 主導来加群圏への K(D) の局所化関手。 -/
def moduleHomotopyToDerivedClosed : ModuleHomotopyCategory A D ⥤ DerivedModuleCategory A D :=
  moduleHomotopyToDerived A D ⋙ (moduleDerivedHomotopyEquivalence A D).inverse

instance moduleHomotopyToDerivedClosedIsLocalization :
    (moduleHomotopyToDerivedClosed A D).IsLocalization (moduleHomotopyQuasiIso A D) := by
  unfold moduleHomotopyToDerivedClosed
  infer_instance

/-- 閉零→K(D)→D(D) と主局所化の比較自然同型。 -/
def moduleToHomotopyDerivedIso :
    moduleToHomotopy A D ⋙ moduleHomotopyToDerivedClosed A D ≅ moduleToDerived A D :=
  (Functor.associator _ _ _).symm ≪≫ moduleDerivedHomotopyInverseComparisonIso A D

end SerrePositivity.DifferentialGraded
