module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementTriangulated

/-! # perfect dg H⁰から主導来圏への整合的三角比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主導来比較の整数shiftを、主Perf比較と既存包含の合成から自然同型で運ぶ。 -/
instance perfectDGModuleToDerivedCommShift (S : Set D) :
    (perfectDGModuleToDerived A D S).CommShift ℤ :=
  Functor.CommShift.ofIso (perfectDGModuleToPerfectCompInclusion A D S) ℤ

/-- 主Perf経由の因子化の自然同型もshiftに整合する。 -/
instance perfectDGModuleToPerfectCompInclusionCommShift (S : Set D) :
    NatTrans.CommShift (perfectDGModuleToPerfectCompInclusion A D S).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (perfectDGModuleToPerfectCompInclusion A D S) ℤ

/-- 主導来比較は三角関手。主Perf比較と既存三角包含の合成から運ぶ。 -/
instance perfectDGModuleToDerivedIsTriangulated (S : Set D) :
    (perfectDGModuleToDerived A D S).IsTriangulated := by
  have : (perfectDGModuleToPerfect A D S ⋙ perfectModuleInclusion A D S).IsTriangulated :=
    inferInstance
  exact Functor.isTriangulated_of_iso (perfectDGModuleToPerfectCompInclusion A D S)

/-- 主導来比較の整合的shiftは、実際のdg shiftから構成した比較と各対象で一致する。 -/
lemma perfectDGModuleToDerived_commShiftIso_hom_app (S : Set D) (s : ℤ)
    (X : PerfectDGHomotopyCategoryOver A D S) :
    ((perfectDGModuleToDerived A D S).commShiftIso s).hom.app X =
      (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X := by
  simp only [Functor.CommShift.ofIso_commShiftIso_hom_app,
    Functor.commShiftIso_comp_hom_app, perfectDGModuleToPerfect_commShiftIso,
    perfectDGModuleToPerfectCompInclusion, ObjectProperty.liftCompιIso,
    Iso.refl_inv, Iso.refl_hom, NatTrans.id_app]
  change 𝟙 ((modulePerfectOver A D S).ι.obj ((perfectDGModuleToPerfect A D S).obj
      ((perfectDGModuleShiftDG A D S s).onHomotopy.obj X))) ≫
    ((modulePerfectOver A D S).ι.map
      ((perfectDGModuleShiftHomotopyPerfectIso A D S s).hom.app X) ≫
      ((modulePerfectOver A D S).ι.commShiftIso s).hom.app
        ((perfectDGModuleToPerfect A D S).obj X)) ≫
      (shiftFunctor (DerivedModuleCategory A D) s).map
        (𝟙 ((modulePerfectOver A D S).ι.obj ((perfectDGModuleToPerfect A D S).obj X))) = _
  simp only [Category.id_comp]
  rw [perfectDGModuleShiftHomotopyPerfectIso_hom_inclusion]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  let Y : DerivedModuleCategory A D := (perfectDGModuleToDerived A D S).obj X
  have h : (shiftFunctor (DerivedModuleCategory A D) s).map (𝟙 Y) = 𝟙 (Y⟦s⟧) :=
    (shiftFunctor (DerivedModuleCategory A D) s).map_id Y
  exact (congrArg (fun a => (perfectDGModuleShiftHomotopyDerivedIso A D S s).hom.app X ≫ a)
    ((Category.id_comp _).trans h)).trans (Category.comp_id _)

end SerrePositivity.DifferentialGraded
