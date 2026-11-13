module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleOutputResolutionClassical
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGModuleMoritaInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedInfinity
public import SerrePositivity.DifferentialGraded.Morita.Kernel
/-!
概要：元の出力分解による一般 kernel 作用を、既存の主導来 tensor 関手と自然同型で比較する。
方針：標準入力分解を射影的入力へ制限し、実 augmentation の自然同型と接続する。
規約：元の出力の射影性・局所 Hom の平坦性を仮定しない。使われ方：一般 Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R]
variable (D : Type v) [DGCategory R D] [Small.{u} D]
  (T : Type v) [DGCategory R T] [Small.{u} T]
/-- 同じ標準入力分解と実出力分解による一般 kernel 作用の主導来比較。 -/
def dgProjectiveClassicalDerivedFunctorIso
    (G : DGFunctor R (RightModule R D) (RightModule R T)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R D ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClassicalDerivedFunctor R D T G ≅
      (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).onHomotopy ⋙
        G.onHomotopy ⋙ moduleHomotopyToDerivedClosed R T :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveDerivedResolutionIso R D)
      (G.onHomotopy ⋙ moduleHomotopyToDerivedClosed R T)
/-- 同じ標準入力分解と実出力分解による一般 kernel 作用の主導来比較。 -/
def dgSemifreeClassicalDerivedFunctorIso
    (G : DGFunctor R (RightModule R D) (RightModule R T)) :
    ((dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)).onHomotopy ⋙
      moduleHomotopyToDerivedClosed R D) ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClassicalDerivedFunctor R D T G ≅
    ((dgFullSubcategoryInclusion R (RightModule R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)).comp G).onHomotopy ⋙
      moduleHomotopyToDerivedClosed R T := by
  let A := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R D
  let J := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
  let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
  have hd : A.comp J = I := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro X Y
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rfl
  have he : A.onHomotopy ⋙ J.onHomotopy = I.onHomotopy := by
    rw [← DGFunctor.onHomotopy_comp, hd]
  have e := Functor.isoWhiskerLeft A.onHomotopy (dgProjectiveClassicalDerivedFunctorIso R D T G)
  change ((A.onHomotopy ⋙ J.onHomotopy) ⋙ moduleHomotopyToDerivedClosed R D) ⋙
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClassicalDerivedFunctor R D T G ≅
    ((A.onHomotopy ⋙ J.onHomotopy) ⋙ G.onHomotopy) ⋙ moduleHomotopyToDerivedClosed R T at e
  rw [he, ← DGFunctor.onHomotopy_comp] at e
  exact e
/-- 同じ標準入力分解と実出力分解による一般 kernel 作用の主導来比較。 -/
def dgKernelOutputResolutionClassicalComparisonIso (P : Bimodule R T D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionClassical R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) T
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D T P) ≅
    ((dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)).onHomotopy ⋙
      moduleHomotopyToDerivedClosed R D) ⋙ Morita.kernelDerivedTensorOnBimodule R D T P :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionClassicalComparisonIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) T
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D T P) ≪≫
      (dgSemifreeClassicalDerivedFunctorIso R D T (Morita.kernelTensor R D T P)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
