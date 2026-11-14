module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeColumnNaturality

/-!
概要：元の native 列の自然性を、HA 方程式と同じ斉次合成の式で述べる。
方針：一点評価の全次数の可換式を、同じ閉零 cycle の合成へ戻す。
規約：元の閉零射と native 列の成分は変えない。
使われ方：3b-3 R6、元の余錐の単体間の全 HA 写像の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の native 列は、元の閉零成分の通常順の斉次合成にも厳密に可換する。 -/
lemma strictBarNativeColumn_cycle_naturality {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    compose A
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (strictBarNormalizedMap A J η)).val
      (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A F)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s)
      (add_zero (-(s.1 : ℤ))) =
    compose A
      (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A G)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) s)
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app (s.2.down.obj 0))).val
      (zero_add (-(s.1 : ℤ))) := by
  change compose A
      (x := ForgetEnrichment.to (Complex A) (F.obj (s.2.down.obj 0)))
      (y := ForgetEnrichment.to (Complex A) ((strictBarNormalizedFunctor A J).obj F))
      (z := ForgetEnrichment.to (Complex A) ((strictBarNormalizedFunctor A J).obj G))
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (strictBarNormalizedMap A J η)).val
      (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A F)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s) (add_zero (-(s.1 : ℤ))) =
    compose A
      (x := ForgetEnrichment.to (Complex A) (F.obj (s.2.down.obj 0)))
      (y := ForgetEnrichment.to (Complex A) (G.obj (s.2.down.obj 0)))
      (z := ForgetEnrichment.to (Complex A) ((strictBarNormalizedFunctor A J).obj G))
      (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A G)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) s)
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app (s.2.down.obj 0))).val
      (zero_add (-(s.1 : ℤ)))
  apply moduleHomElement_ext A PUnit.{1}
    (M := ForgetEnrichment.to (Complex A) (F.obj (s.2.down.obj 0)))
    (N := ForgetEnrichment.to (Complex A) ((strictBarNormalizedFunctor A J).obj G))
  rintro ⟨⟩
  have hn := moduleEvaluation_cochain A PUnit.{1} PUnit.unit (strictBarNormalizedMap A J η)
  change Cochain.ofHom ((moduleEvaluation A PUnit.{1} PUnit.unit).map
      (strictBarNormalizedMap A J η)) =
    (moduleHomπ A PUnit.{1}
      (ForgetEnrichment.to (Complex A) ((strictBarNormalizedFunctor A J).obj F))
      (ForgetEnrichment.to (Complex A) ((strictBarNormalizedFunctor A J).obj G)) PUnit.unit).f 0
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (strictBarNormalizedMap A J η)).val at hn
  have hs := moduleEvaluation_cochain A PUnit.{1} PUnit.unit (η.app (s.2.down.obj 0))
  change Cochain.ofHom ((moduleEvaluation A PUnit.{1} PUnit.unit).map (η.app (s.2.down.obj 0))) =
    (moduleHomπ A PUnit.{1}
      (ForgetEnrichment.to (Complex A) (F.obj (s.2.down.obj 0)))
      (ForgetEnrichment.to (Complex A) (G.obj (s.2.down.obj 0))) PUnit.unit).f 0
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app (s.2.down.obj 0))).val at hs
  rw [moduleHomCompose_π, moduleHomCompose_π, ← hn, ← hs]
  apply Cochain.ext
  intro q r hqr
  simpa only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using!
    (strictBarNativeColumn_point_naturality A J η s q r hqr).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
