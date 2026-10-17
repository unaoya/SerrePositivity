module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarDerivedPerfect

/-! # 元と係数変更後のenhancementの閉零圏・H⁰を結ぶ実際の関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 係数環の異なる二つのenhancementの閉零圏間の、実際の加群係数拡大。 -/
def scalarPerfectClosedExtension (S : Set D) :
    ClosedCategory A (PerfectDGModuleOver A D S) ⥤
      ClosedCategory A' (PerfectDGModuleOver A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S)) where
  obj M := by
    let M' : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) M
    exact ForgetEnrichment.of (Complex A')
      (⟨ScalarExtension.rightModule φ D M'.val,
        scalarModuleExtension_projective_perfect φ D M'.property.1 M'.property.2,
        scalarModuleExtension_perfect_perfect φ D M'.property.1 M'.property.2⟩ :
        PerfectDGModuleOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S))
  map {M N} f := by
    let M' : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) M
    let N' : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) N
    change 𝟙_ (Complex A') ⟶ moduleHom A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D M'.val) (ScalarExtension.rightModule φ D N'.val)
    let f' : ForgetEnrichment.of (Complex A) M'.val ⟶
        ForgetEnrichment.of (Complex A) N'.val :=
      (perfectDGModuleInclusion A D S).onClosed.map f
    exact ForgetEnrichment.homTo (Complex A') ((ScalarExtension.moduleExtension φ D).map f')
  map_id M := by
    change (ScalarExtension.moduleExtension φ D).map
      ((perfectDGModuleInclusion A D S).onClosed.map (𝟙 M)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    change (ScalarExtension.moduleExtension φ D).map
      ((perfectDGModuleInclusion A D S).onClosed.map (f ≫ g)) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl

def scalarPerfectClosedInclusionIso (S : Set D) :
    scalarPerfectClosedExtension φ D S ⋙
        (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)).onClosed ≅
      (perfectDGModuleInclusion A D S).onClosed ⋙ ScalarExtension.moduleExtension φ D :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl)

def scalarPerfectHomotopyExtension (S : Set D) :
    PerfectDGHomotopyCategoryOver A D S ⥤
      PerfectDGHomotopyCategoryOver A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S) :=
  CategoryTheory.Quotient.lift _ (scalarPerfectClosedExtension φ D S ⋙
    toHomotopy A' (PerfectDGModuleOver A' (ScalarExtension.DGBaseChange φ D)
      (scalarPerfectGenerators φ D S))) (by
      intro M N f g hb
      apply (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S)).onHomotopy.map_injective
      have h := (perfectDGModuleInclusion A D S).preserves_boundary f g hb
      obtain ⟨hh⟩ := (moduleHomotopy_nonempty_iff A D _ _).2 h
      change (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)).map
          ((ScalarExtension.moduleExtension φ D).map
            ((perfectDGModuleInclusion A D S).onClosed.map f)) =
        (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)).map
          ((ScalarExtension.moduleExtension φ D).map
            ((perfectDGModuleInclusion A D S).onClosed.map g))
      exact (moduleToHomotopy_map_eq_iff A' (ScalarExtension.DGBaseChange φ D) _ _).2
        ⟨scalarModuleHomotopy φ D hh⟩)

lemma scalarPerfectHomotopyExtension_fac (S : Set D) :
    toHomotopy A (PerfectDGModuleOver A D S) ⋙ scalarPerfectHomotopyExtension φ D S =
      scalarPerfectClosedExtension φ D S ⋙
        toHomotopy A' (PerfectDGModuleOver A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)) :=
  CategoryTheory.Quotient.lift_spec _ _ _

def scalarPerfectClosedDerivedIso (S : Set D) :
    (perfectDGModuleInclusion A D S).onClosed ⋙ moduleToDerived A D ⋙
        ScalarExtension.derivedExtension φ D ≅
      scalarPerfectClosedExtension φ D S ⋙
        (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)).onClosed ⋙
            moduleToDerived A' (ScalarExtension.DGBaseChange φ D) := by
  let I := (perfectDGModuleInclusion A D S).onClosed
  let a := Functor.whiskerLeft I (ScalarExtension.derivedExtensionAugmentation φ D)
  have (M : ClosedCategory A (PerfectDGModuleOver A D S)) : IsIso (a.app M) :=
    scalarDerivedExtensionAugmentation_isIso_of_projective φ D (I.obj M)
      (ForgetEnrichment.to (Complex A) M).property.1
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a ≪≫ Functor.isoWhiskerRight (scalarPerfectClosedInclusionIso φ D S).symm
    (moduleToDerived A' (ScalarExtension.DGBaseChange φ D))

end SerrePositivity.DifferentialGraded
