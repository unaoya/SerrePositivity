module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeColumnValues

/-!
概要：元の native 余錐列が、元の strict 自然変換に全内部次数で可換することを示す。
方針：元の符号付き shift 包含と同じ正規化列の二つの自然性を合成する。
規約：自然性を入力にはせず、退化ラベルも含めて同じ列で証明する。
使われ方：3b-3 R6、指定余錐の元の全 HA 成分を保つ族の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の native 列は、元の先頭の射と元の正規化 bar の射に可換する。 -/
lemma strictBarNativeColumn_point_naturality {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J)))
    (q r : ℤ) (hqr : q + -(s.1 : ℤ) = r) :
    ((moduleEvaluation A PUnit.{1} PUnit.unit).map (η.app (s.2.down.obj 0))).f q ≫
      (((moduleHomπ A PUnit.{1}
        (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A G) s)
        (dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A G))
        PUnit.unit).f (-(s.1 : ℤ))
          (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A G)
            (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) s)).v q r hqr) =
      (((moduleHomπ A PUnit.{1}
        (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s)
        (dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F))
        PUnit.unit).f (-(s.1 : ℤ))
          (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A F)
            (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s)).v q r hqr) ≫
        ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarNormalizedMap A J η)).f r := by
  rw [strictBarNativeColumn_point, strictBarNativeColumn_point,
    strictBarNormalizedMap_component]
  simp only [smallStrictBarDiagram_source]
  have hs := pointShiftInElement_naturality A (s.1 : ℤ) (η.app (s.2.down.obj 0)) q r hqr
  have hc := congrArg (fun f => ((moduleEvaluation A PUnit.{1} PUnit.unit).map f).f r)
    (strictBarNormalizedColumn_naturality A J η s)
  simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at hc
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc]
  congr 1
  rw [← Category.assoc, hs, Category.assoc, ← hc]

/-- 元の native 列の同じ可換式を、全 Hom の斉次元として述べる。 -/
lemma strictBarNativeColumn_naturality {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    (eHomWhiskerRight (Complex A) (η.app (s.2.down.obj 0))
      ((strictBarNormalizedFunctor A J).obj G)).f (-(s.1 : ℤ))
        (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A G)
          (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) s) =
      (eHomWhiskerLeft (Complex A) (F.obj (s.2.down.obj 0))
        (strictBarNormalizedMap A J η)).f (-(s.1 : ℤ))
          (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A F)
            (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s) := by
  apply moduleHomElement_ext A PUnit.{1}
    (M := ForgetEnrichment.to (Complex A) (F.obj (s.2.down.obj 0)))
    (N := ForgetEnrichment.to (Complex A) ((strictBarNormalizedFunctor A J).obj G))
  rintro ⟨⟩
  apply Cochain.ext
  intro q r hqr
  have heR := moduleHomWhiskerRight_apply_π A PUnit.{1}
    (M := F.obj (s.2.down.obj 0)) (N := G.obj (s.2.down.obj 0))
    (P := (strictBarNormalizedFunctor A J).obj G) (η.app (s.2.down.obj 0))
    (-(s.1 : ℤ))
    (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A G)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) s) PUnit.unit
  have heL := moduleHomWhiskerLeft_apply_π A PUnit.{1} (T := F.obj (s.2.down.obj 0))
    (M := (strictBarNormalizedFunctor A J).obj F)
    (N := (strictBarNormalizedFunctor A J).obj G) (strictBarNormalizedMap A J η)
    (-(s.1 : ℤ))
    (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A F)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s) PUnit.unit
  have hr := congrArg (fun z => z.v q r hqr) heR
  have hl := congrArg (fun z => z.v q r hqr) heL
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at hr hl
  exact hr.trans ((strictBarNativeColumn_point_naturality A J η s q r hqr).trans hl.symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
