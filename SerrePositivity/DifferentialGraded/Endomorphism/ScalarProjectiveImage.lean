module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectHom
public import SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveCriterion

/-! # 実際の係数拡大によるperfect射影的加群の射影性保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

instance scalarModuleExtensionAdditive : (ScalarExtension.moduleExtension φ D).Additive where
  map_add {X Y} {f g} := by
    apply moduleMorphism_ext
    intro x
    simp only [Functor.map_add, ScalarExtension.moduleExtension_eval]

lemma scalarModuleExtension_projective_shift (s : ℤ) (M : RightModule A D)
    (hM : moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj (ForgetEnrichment.of (Complex A) M))) :
    moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj
        (ForgetEnrichment.of (Complex A) (shiftModule s M))) := by
  intro N hN
  exact cochainAcyclic_of_iso (cochainAcyclic_shift (hM N hN) (-s))
    (scalarModuleShiftOppImageIso φ D
      ((scalarModuleDGFunctor φ D).op.comp
        (representable A' (ForgetEnrichment.to (Complex A') N))) s M).symm

lemma scalarModuleExtension_projective_finiteCellCode {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) :
    moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj M) := by
  let F := ScalarExtension.moduleExtension φ D
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  induction c with
  | zero =>
      exact moduleHomotopicallyProjective_of_isZero A' (ScalarExtension.DGBaseChange φ D)
        (F.map_isZero (moduleZero_isZero A D))
  | generator x hx =>
      change moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
        (ForgetEnrichment.of (Complex A') (ScalarExtension.rightModule φ D (representable A x)))
      rw [scalarRepresentable_eq]
      exact representable_homotopicallyProjective A' (ScalarExtension.DGBaseChange φ D) x
  | @shift M s c ih =>
      exact scalarModuleExtension_projective_shift φ D s (ForgetEnrichment.to (Complex A) M) ih
  | @sum M N c d ihc ihd =>
      let e := F.mapIso (moduleBiprodIso A D M N) ≪≫ F.mapBiprod M N ≪≫
        (moduleBiprodIso A' (ScalarExtension.DGBaseChange φ D) (F.obj M) (F.obj N)).symm
      exact moduleHomotopicallyProjective_of_iso A' (ScalarExtension.DGBaseChange φ D) e.symm
        (moduleHomotopicallyProjective_biprod A' (ScalarExtension.DGBaseChange φ D) ihc ihd)
  | @cone M N c d f ihc ihd =>
      exact (scalarModuleGradedSplit φ D (moduleConeGradedSplit A D f)).homotopicallyProjective
        A' (ScalarExtension.DGBaseChange φ D) ihd
          (scalarModuleExtension_projective_shift φ D 1 (ForgetEnrichment.to (Complex A) M) ihc)
  | iso c e ih =>
      exact moduleHomotopicallyProjective_of_iso A' (ScalarExtension.DGBaseChange φ D)
        (F.mapIso e) ih

lemma scalarModuleExtension_projective_finiteCell {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) :
    moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj M) := by
  obtain ⟨c⟩ := hM
  exact scalarModuleExtension_projective_finiteCellCode φ D c

lemma scalarModuleExtension_projective_perfect {S : Set D} {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M)
    (hPerf : modulePerfectOver A D S ((moduleToDerived A D).obj M)) :
    moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj M) := by
  let F := ScalarExtension.moduleExtension φ D
  obtain ⟨N, hN, ⟨a⟩⟩ := (modulePerfectOver_iff A D S _).mp hPerf
  have hNP := moduleFiniteCellOver_homotopicallyProjective A D hN
  obtain ⟨i, hi⟩ := moduleProjectiveToDerived_map_surjective A D hM a.i
  obtain ⟨r, hr⟩ := moduleProjectiveToDerived_map_surjective A D hNP a.r
  have h : (moduleToHomotopy A D).map (i ≫ r) = (moduleToHomotopy A D).map (𝟙 M) := by
    apply (moduleProjectiveDerivedHomEquiv A D hM M).injective
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
      Functor.map_comp, hi, hr, a.retract, CategoryTheory.Functor.map_id]
  apply moduleHomotopicallyProjective_of_homotopyRetract A'
    (ScalarExtension.DGBaseChange φ D) (F.map i) (F.map r) _
      (scalarModuleExtension_projective_finiteCell φ D hN)
  have he := congrArg (scalarModuleExtensionHomotopy φ D).map h
  change (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)).map (F.map (i ≫ r)) =
    (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)).map (F.map (𝟙 M)) at he
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using he

end SerrePositivity.DifferentialGraded
