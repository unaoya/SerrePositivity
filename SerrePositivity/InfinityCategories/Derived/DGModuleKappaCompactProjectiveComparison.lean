module
public import SerrePositivity.InfinityCategories.DoldKanComparison.ComparisonEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGModuleKappaCompactShift
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeProjectiveEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

abbrev dgProjectiveDerivedHoComparison :=
  (dgStableHomotopyEquivalence R (ProjectiveDGModules R D)).functor ⋙
    dgProjectiveModuleToDerived R D

def dgProjectiveVertex_classicalIso (M : ProjectiveDGModules R D) :
    (dgProjectiveDerivedHoComparison R D).obj
      (SSet.HomotopyCategory.mk (Simplex.vertex M)) ≅
        (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R) M.val) :=
  (moduleToHomotopyDerivedIso R D).app _

def dgConeModuleDerivedProjectiveImage_classicalIso (M : ModuleCategory R D) :
    (dgProjectiveDerivedHoComparison R D).obj
      ((hoFunctor.map (dgNerve.map (dgSemifreeToProjective R D))).toFunctor.obj
        (SSet.HomotopyCategory.mk (dgConeModuleDerivedVertex R D M))) ≅
      (moduleToDerived R D).obj M :=
  (Functor.isoWhiskerRight
    (dgStableHomotopyEquivalence_naturalityIso R _ _ (dgSemifreeToProjective R D))
    (dgProjectiveModuleToDerived R D)).app _ ≪≫
    dgConeModuleDerivedVertex_classicalIso R D M

def dgConeModuleDerivedProjectiveImageIso (M : ProjectiveDGModules R D) :
    VertexIso
      ((dgNerve.map (dgSemifreeToProjective R D)).app _
        (dgConeModuleDerivedVertex R D (ForgetEnrichment.of (Complex R) M.val)))
      (Simplex.vertex M) :=
  (dgProjectiveDerivedHoComparison R D).preimageIso
    (dgConeModuleDerivedProjectiveImage_classicalIso R D _ ≪≫
      (dgProjectiveVertex_classicalIso R D M).symm)

lemma dgModuleKappaCompact_iff_projectiveVertex {κ : Cardinal.{u}}
    (M : ProjectiveDGModules R D) :
    dgModuleKappaCompact R D κ (ForgetEnrichment.of (Complex R) M.val) ↔
      F2.Compact.IsKappaCompact.{u, max (u+1) v}
        (C := dgProjectiveModuleNerve R D) κ (Simplex.vertex M) := by
  have h := F2.Presentable.isKappaCompact_iff_equivalence_universe.{u, max (u+1) v}
    (κ := κ) (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose
    (dgConeModuleDerivedVertex R D (ForgetEnrichment.of (Complex R) M.val))
  exact h.trans (F2.Compact.isKappaCompact_iff_of_iso.{u, max (u+1) v}
    (dgConeModuleDerivedProjectiveImageIso R D M))

lemma dgModuleKappaCompact_iff_projectiveCoherentVertex {κ : Cardinal.{u}}
    (M : ProjectiveDGModules R D) :
    dgModuleKappaCompact R D κ (ForgetEnrichment.of (Complex R) M.val) ↔
      F2.Compact.IsKappaCompact.{u, max (u+1) v}
        (C := DoldKanComparison.doldKanCoherentNerve (R := R) (D := ProjectiveDGModules R D))
        κ (DoldKanComparison.coherentVertex (R := R) M) := by
  have h := F2.Presentable.isKappaCompact_iff_equivalence_universe.{u, max (u+1) v}
    (κ := κ) (DoldKanComparison.coherentComparisonEquivalence
      (R := R) (D := ProjectiveDGModules R D))
    (DoldKanComparison.coherentVertex (R := R) M)
  rw [DoldKanComparison.coherentComparisonEquivalence_hom,
    DoldKanComparison.coherentComparison_vertex] at h
  exact (dgModuleKappaCompact_iff_projectiveVertex R D M).trans h.symm

end SerrePositivity.InfinityCategories
