module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComparisonEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactShift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeProjectiveEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyNaturality
/-!
概要：元の実導来加群頂点と、同じ射影的加群の dg 頂点の κ-compact 性を比較する。
方針：半自由包含の h 自然性と実導来比較で頂点同型を作り、P-9 の同値保存を使う。
規約：主導来圏は同型を作るためだけに使用し、ordinary compact 性を仮定しない。
使われ方：D-8 c5 の射影的直和余錐を元の半自由模型へ戻す比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

abbrev dgProjectiveDerivedHoComparison :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)).functor ⋙
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R D

def dgProjectiveVertex_classicalIso (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) :
    (dgProjectiveDerivedHoComparison R D).obj
      (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)) ≅
        (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M.val) :=
  (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app _

def dgConeModuleDerivedProjectiveImage_classicalIso (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    (dgProjectiveDerivedHoComparison R D).obj
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R D))).toFunctor.obj
        (SSet.HomotopyCategory.mk (dgConeModuleDerivedVertex R D M))) ≅
      (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj M :=
  (Functor.isoWhiskerRight
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_naturalityIso R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R D)).app _ ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso R D M

def dgConeModuleDerivedProjectiveImageIso (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R D)).app _
        (dgConeModuleDerivedVertex R D (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M.val)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) :=
  (dgProjectiveDerivedHoComparison R D).preimageIso
    (dgConeModuleDerivedProjectiveImage_classicalIso R D _ ≪≫
      (dgProjectiveVertex_classicalIso R D M).symm)

lemma dgModuleKappaCompact_iff_projectiveVertex {κ : Cardinal.{u}}
    (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (ForgetEnrichment.of (Complex R) M.val) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u+1) v}
        (C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D) κ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_iff_equivalence_universe.{u, max (u+1) v}
    (κ := κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose
    (dgConeModuleDerivedVertex R D (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M.val))
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso.{u, max (u+1) v}
    (dgConeModuleDerivedProjectiveImageIso R D M))

lemma dgModuleKappaCompact_iff_projectiveCoherentVertex {κ : Cardinal.{u}}
    (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (ForgetEnrichment.of (Complex R) M.val) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u+1) v}
        (C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D))
        κ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) M) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_iff_equivalence_universe.{u, max (u+1) v}
    (κ := κ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparisonEquivalence
      (R := R) (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) M)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparisonEquivalence_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_vertex] at h
  exact (dgModuleKappaCompact_iff_projectiveVertex R D M).trans h.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
