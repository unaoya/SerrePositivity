module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModules
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-!
概要：射影的右 dg 加群の H⁰ と、既存の主導来加群圏の比較同値。
方針：全 Hom end の射影性による実局所化 Hom 計算と、具体的射影分解を使う。
規約：∞ 圏の同値は別途全 Hom 鎖写像を検査する。使われ方：β5 の Morita 条件の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 射影的加群の実 H⁰ から、既存の主導来加群圏への比較。 -/
def dgProjectiveModuleToDerived : HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) ⥤
    DerivedModuleCategory R D :=
  (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).onHomotopy ⋙
    moduleHomotopyToDerivedClosed R D
/-- 射影的加群からの主導来比較は充満。 -/
instance dgProjectiveModuleToDerived_full : (dgProjectiveModuleToDerived R D).Full where
  map_surjective {X Y} f := by
    let M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D := ForgetEnrichment.to (Complex R) X.as
    let N : ModuleCategory R D := ForgetEnrichment.of (Complex R) M.val
    let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
    obtain ⟨g, hg⟩ := (moduleProjectiveLocalization_map_bijective R D
      (P := N) M.property (I.onHomotopy.obj Y)).2 f
    obtain ⟨h, hh⟩ := I.onHomotopy.map_surjective g
    refine ⟨h, ?_⟩
    change (moduleHomotopyToDerivedClosed R D).map (I.onHomotopy.map h) = f
    rw [hh]
    exact hg
/-- 射影的加群からの主導来比較は忠実。 -/
instance dgProjectiveModuleToDerived_faithful : (dgProjectiveModuleToDerived R D).Faithful where
  map_injective {X Y} f g h := by
    let M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D := ForgetEnrichment.to (Complex R) X.as
    let N : ModuleCategory R D := ForgetEnrichment.of (Complex R) M.val
    let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
    apply I.onHomotopy.map_injective
    exact (moduleProjectiveLocalization_map_bijective R D
      (P := N) M.property (I.onHomotopy.obj Y)).1 h
/-- 具体的射影分解による、射影的加群からの主導来比較の本質的全射性。 -/
instance dgProjectiveModuleToDerived_essSurj : (dgProjectiveModuleToDerived R D).EssSurj where
  mem_essImage X := by
    let P := moduleCanonicalProjectiveResolution R D X.as.obj
    let M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D := ⟨ForgetEnrichment.to (Complex R) P.obj, P.projective⟩
    refine ⟨(toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)).obj
      (ForgetEnrichment.of (Complex R) M), ⟨?_⟩⟩
    exact (moduleToHomotopyDerivedIso R D).app P.obj ≪≫ moduleDerivedIso R D P.π P.quasiIso
/-- 射影的加群からの主導来比較は同値。 -/
instance dgProjectiveModuleToDerived_isEquivalence :
    (dgProjectiveModuleToDerived R D).IsEquivalence where
/-- 射影的加群の H⁰ と既存の主導来加群圏の具体的同値。 -/
def dgProjectiveModuleDerivedEquivalence : HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) ≌
    DerivedModuleCategory R D := (dgProjectiveModuleToDerived R D).asEquivalence
end SerrePositivity.InfinityCategories.Project.DerivedCategories
