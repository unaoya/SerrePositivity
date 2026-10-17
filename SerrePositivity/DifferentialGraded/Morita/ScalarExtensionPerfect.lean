module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectImage
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension

/-! # U16d：非flatな導来係数変更の主Perf制限

U14で証明した射影的perfect代表の実際の係数拡大のperfect性を、
U12fの既存導来係数拡大の任意射影解像度計算で主導来圏へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarDerivedExtension_perfectOver {S : Set D} {X : DerivedModuleCategory A D}
    (hX : modulePerfectOver A D S X) :
    modulePerfectOver A' (DGBaseChange φ D) (scalarPerfectGenerators φ D S)
      ((derivedExtension φ D).obj X) := by
  obtain ⟨⟨M⟩⟩ := X
  let P := moduleCanonicalProjectiveResolution A D M
  have hP : modulePerfectOver A D S ((moduleToDerived A D).obj P.obj) :=
    (modulePerfectOver A D S).prop_of_iso (moduleDerivedIso A D P.π P.quasiIso).symm hX
  exact (modulePerfectOver A' (DGBaseChange φ D) (scalarPerfectGenerators φ D S)).prop_of_iso
    (derivedExtensionResolutionComputation φ D P).symm
    (scalarModuleExtension_perfect_perfect φ D P.projective hP)

lemma scalarDerivedExtension_perfect {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A' (DGBaseChange φ D) ((derivedExtension φ D).obj X) :=
  scalarDerivedExtension_perfectOver φ D hX

def scalarExtensionPerfectFunctor (S : Set D) :
    PerfectModuleCategoryOver A D S ⥤
      PerfectModuleCategoryOver A' (DGBaseChange φ D) (scalarPerfectGenerators φ D S) :=
  (modulePerfectOver A' (DGBaseChange φ D) (scalarPerfectGenerators φ D S)).lift
    (perfectModuleInclusion A D S ⋙ derivedExtension φ D)
    (fun X => scalarDerivedExtension_perfectOver φ D X.property)

def scalarExtensionPerfectInclusionIso (S : Set D) :
    scalarExtensionPerfectFunctor φ D S ⋙
        perfectModuleInclusion A' (DGBaseChange φ D) (scalarPerfectGenerators φ D S) ≅
      perfectModuleInclusion A D S ⋙ derivedExtension φ D := Iso.refl _

end SerrePositivity.DifferentialGraded.Morita
