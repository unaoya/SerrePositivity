module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveDerivedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeModules
/-!
概要：半自由加群の H⁰ から元の主導来加群圏への包含・局所化の比較同値を構成する。
方針：半自由始域の射影性による局所化 Hom の計算と、同じ実半自由分解を使う。
規約：∞ 圏の同値は全高次 Hom の検査後に結論する。使われ方：一般 Morita 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 半自由加群の実 H⁰ から、既存の主導来加群圏への比較。 -/
def dgSemifreeModuleToDerived : HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) ⥤
    DerivedModuleCategory R D :=
  (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)).onHomotopy ⋙
    moduleHomotopyToDerivedClosed R D
/-- 半自由加群からの主導来比較は充満。 -/
instance dgSemifreeModuleToDerived_full : (dgSemifreeModuleToDerived R D).Full where
  map_surjective {X Y} f := by
    let M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D := ForgetEnrichment.to (Complex R) X.as
    let N : ModuleCategory R D := ForgetEnrichment.of (Complex R) M.val
    let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
    obtain ⟨g, hg⟩ := (moduleProjectiveLocalization_map_bijective R D
      (P := N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D M) (I.onHomotopy.obj Y)).2 f
    obtain ⟨h, hh⟩ := I.onHomotopy.map_surjective g
    refine ⟨h, ?_⟩
    change (moduleHomotopyToDerivedClosed R D).map (I.onHomotopy.map h) = f
    rw [hh]
    exact hg
/-- 半自由加群からの主導来比較は忠実。 -/
instance dgSemifreeModuleToDerived_faithful : (dgSemifreeModuleToDerived R D).Faithful where
  map_injective {X Y} f g h := by
    let M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D := ForgetEnrichment.to (Complex R) X.as
    let N : ModuleCategory R D := ForgetEnrichment.of (Complex R) M.val
    let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
    apply I.onHomotopy.map_injective
    exact (moduleProjectiveLocalization_map_bijective R D
      (P := N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D M) (I.onHomotopy.obj Y)).1 h
/-- 具体的半自由分解による、半自由加群からの主導来比較の本質的全射性。 -/
instance dgSemifreeModuleToDerived_essSurj : (dgSemifreeModuleToDerived R D).EssSurj where
  mem_essImage X := by
    obtain ⟨P, π, _, hπ⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_resolution_exists R D
      (ForgetEnrichment.to (Complex R) X.as.obj)
    refine ⟨(toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).obj
      (ForgetEnrichment.of (Complex R) P), ⟨?_⟩⟩
    exact (moduleToHomotopyDerivedIso R D).app (ForgetEnrichment.of (Complex R) P.val) ≪≫
      moduleDerivedIso R D π hπ
/-- 半自由加群からの主導来比較は同値。 -/
instance dgSemifreeModuleToDerived_isEquivalence :
    (dgSemifreeModuleToDerived R D).IsEquivalence where
end SerrePositivity.InfinityCategories.Project.DerivedCategories
