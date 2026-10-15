module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveLocalizationHom
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolution
public import Mathlib.CategoryTheory.EssentiallySmall

/-! # 射影解像度による導来圏の射集合と局所小性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 任意の証明付き射影解像度で実際の導来圏の射集合を計算する。 -/
def moduleResolutionDerivedHomEquiv {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (N : ModuleCategory A D) :
    ((moduleToHomotopy A D).obj P.obj ⟶ (moduleToHomotopy A D).obj N) ≃
      ((moduleToDerived A D).obj M ⟶ (moduleToDerived A D).obj N) :=
  (moduleProjectiveDerivedHomEquiv A D P.projective N).trans
    (Iso.homCongr (moduleDerivedIso A D P.π P.quasiIso) (Iso.refl _))

lemma moduleResolutionDerivedHomEquiv_map {M N : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (f : P.obj ⟶ N) :
    moduleResolutionDerivedHomEquiv A D P N ((moduleToHomotopy A D).map f) =
      (moduleDerivedIso A D P.π P.quasiIso).inv ≫ (moduleToDerived A D).map f := by
  change (moduleDerivedIso A D P.π P.quasiIso).inv ≫
    moduleProjectiveDerivedHomEquiv A D P.projective N ((moduleToHomotopy A D).map f) ≫ 𝟙 _ = _
  rw [moduleProjectiveDerivedHomEquiv_map, Category.comp_id]

/-- 任意の導来射は指定解像度の増大射を左分母とするroofで表せる。 -/
lemma moduleResolutionDerivedHom_surjective {M N : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M)
    (g : (moduleToDerived A D).obj M ⟶ (moduleToDerived A D).obj N) :
    ∃ f : P.obj ⟶ N,
      (moduleDerivedIso A D P.π P.quasiIso).inv ≫ (moduleToDerived A D).map f = g := by
  obtain ⟨f, hf⟩ := (moduleResolutionDerivedHomEquiv A D P N).surjective g
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  exact ⟨f, (moduleResolutionDerivedHomEquiv_map A D P f).symm.trans hf⟩

lemma moduleResolutionDerivedHom_eq_iff {M N : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (f g : P.obj ⟶ N) :
    (moduleDerivedIso A D P.π P.quasiIso).inv ≫ (moduleToDerived A D).map f =
      (moduleDerivedIso A D P.π P.quasiIso).inv ≫ (moduleToDerived A D).map g ↔
        Nonempty (ModuleHomotopy A D f g) := by
  rw [← moduleResolutionDerivedHomEquiv_map A D P f,
    ← moduleResolutionDerivedHomEquiv_map A D P g,
    (moduleResolutionDerivedHomEquiv A D P N).injective.eq_iff,
    moduleToHomotopy_map_eq_iff]

lemma moduleDerivedHom_small (M N : ModuleCategory A D) :
    Small.{u} ((moduleToDerived A D).obj M ⟶ (moduleToDerived A D).obj N) := by
  exact small_of_surjective
    (moduleResolutionDerivedHomEquiv A D (moduleCanonicalProjectiveResolution A D M) N).surjective

instance moduleDerivedLocallySmall : LocallySmall.{u} (DerivedModuleCategory A D) where
  hom_small M N := by
    obtain ⟨⟨M⟩⟩ := M
    obtain ⟨⟨N⟩⟩ := N
    exact moduleDerivedHom_small A D M N

end SerrePositivity.DifferentialGraded
