module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectImage
public import SerrePositivity.DifferentialGraded.Endomorphism.QuasiFullyFaithful

/-! # 実際の係数拡大のU13 enhancementへの制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 係数変更したU13 enhancementから、実際の係数変更加群のenhancementへの比較。 -/
def scalarPerfectDG (S : Set D) :
    DGFunctor A' (ScalarExtension.DGBaseChange φ (PerfectDGModuleOver A D S))
      (PerfectDGModuleOver A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S)) where
  obj M := ⟨ScalarExtension.rightModule φ D M.val,
    scalarModuleExtension_projective_perfect φ D M.property.1 M.property.2,
    scalarModuleExtension_perfect_perfect φ D M.property.1 M.property.2⟩
  map M N := scalarModuleHom φ D M.val N.val
  map_id M := scalarModuleHom_identity φ D M.val
  map_comp M N P := scalarModuleHom_composition φ D M.val N.val P.val

lemma scalarPerfectDG_homQuasiIso (S : Set D) : HomQuasiIso (scalarPerfectDG φ D S) := by
  intro M N
  exact scalarModuleHom_quasiIso_of_perfect φ D M.property.1 M.property.2
    (ForgetEnrichment.of (Complex A) N.val)

instance scalarPerfectDGHomotopyFull (S : Set D) :
    (scalarPerfectDG φ D S).onHomotopy.Full :=
  dgHomMap_onHomotopy_full _ (scalarPerfectDG_homQuasiIso φ D S)

instance scalarPerfectDGHomotopyFaithful (S : Set D) :
    (scalarPerfectDG φ D S).onHomotopy.Faithful :=
  dgHomMap_onHomotopy_faithful _ (scalarPerfectDG_homQuasiIso φ D S)

lemma scalarPerfectDG_inclusion_square (S : Set D) :
    (scalarPerfectDG φ D S).comp
        (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)) =
      (ScalarExtension.dgFunctor φ (perfectDGModuleInclusion A D S)).comp
        (scalarModuleDGFunctor φ D) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (scalarPerfectDG φ D S).comp
      (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S)))
    (G := (ScalarExtension.dgFunctor φ (perfectDGModuleInclusion A D S)).comp
      (scalarModuleDGFunctor φ D)) (fun _ => rfl)
  intro M N
  change scalarModuleHom φ D M.val N.val ≫ 𝟙 _ =
    (ScalarExtension.extension φ).map (𝟙 _) ≫ scalarModuleHom φ D M.val N.val
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end SerrePositivity.DifferentialGraded
