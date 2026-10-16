module
public import SerrePositivity.DifferentialGraded.Perfect.Shift
public import SerrePositivity.CategoryTheory.KaroubiFullyFaithful
public import SerrePositivity.CategoryTheory.KaroubiTriangulatedFunctor

/-! # Perfとfinite cell部分圏のKaroubi延長の本質像 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定導来圏内のfinite cellの本質的像の充満部分圏。 -/
abbrev DerivedFiniteCellCategoryOver (S : Set D) := (derivedFiniteCellOver A D S).FullSubcategory

def derivedFiniteCellInclusion (S : Set D) :
    DerivedFiniteCellCategoryOver A D S ⥤ DerivedModuleCategory A D :=
  (derivedFiniteCellOver A D S).ι

instance derivedFiniteCellInclusionFull (S : Set D) :
    (derivedFiniteCellInclusion A D S).Full := by
  dsimp [derivedFiniteCellInclusion]
  infer_instance

instance derivedFiniteCellInclusionFaithful (S : Set D) :
    (derivedFiniteCellInclusion A D S).Faithful := by
  dsimp [derivedFiniteCellInclusion]
  infer_instance

instance derivedFiniteCellInclusionCommShift (S : Set D) :
    (derivedFiniteCellInclusion A D S).CommShift ℤ := by
  dsimp [derivedFiniteCellInclusion]
  infer_instance

/-- 既存一般APIで構成する、finite cell包含のKaroubi延長。 -/
def finiteCellKaroubiFunctor (S : Set D) :
    Karoubi (DerivedFiniteCellCategoryOver A D S) ⥤ Karoubi (DerivedModuleCategory A D) :=
  (functorExtension₂ _ _).obj (derivedFiniteCellInclusion A D S)

instance finiteCellKaroubiFunctorFull (S : Set D) : (finiteCellKaroubiFunctor A D S).Full := by
  dsimp [finiteCellKaroubiFunctor]
  infer_instance

instance finiteCellKaroubiFunctorFaithful (S : Set D) :
    (finiteCellKaroubiFunctor A D S).Faithful := by
  dsimp [finiteCellKaroubiFunctor]
  infer_instance

/-- Karoubi延長は元のfinite cell包含と自然同型で可換。 -/
def finiteCellKaroubiFunctor_fac (S : Set D) :
    toKaroubi (DerivedFiniteCellCategoryOver A D S) ⋙ finiteCellKaroubiFunctor A D S ≅
      derivedFiniteCellInclusion A D S ⋙ toKaroubi (DerivedModuleCategory A D) :=
  (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app (derivedFiniteCellInclusion A D S)

/-- D(D)内のperfect対象は、Karoubi延長の本質像に入る対象と正確に一致する。 -/
lemma modulePerfectOver_iff_karoubi_essImage (S : Set D) (X : DerivedModuleCategory A D) :
    modulePerfectOver A D S X ↔
      (finiteCellKaroubiFunctor A D S).essImage
        ((toKaroubi (DerivedModuleCategory A D)).obj X) := by
  constructor
  · rintro ⟨Y, hY, ⟨r⟩⟩
    exact karoubiExtension_mem_essImage (derivedFiniteCellInclusion A D S)
      ((toKaroubi (DerivedModuleCategory A D)).obj X) ⟨Y, hY⟩
      (r.map (toKaroubi (DerivedModuleCategory A D)))
  · rintro ⟨P, ⟨e⟩⟩
    let rK : Retract ((toKaroubi (DerivedModuleCategory A D)).obj X)
        ((toKaroubi (DerivedModuleCategory A D)).obj P.X.obj) :=
      ((Retract.ofIso e.symm).trans
        ((karoubiRetract P).map (finiteCellKaroubiFunctor A D S))).trans
          (Retract.ofIso ((finiteCellKaroubiFunctor_fac A D S).app P.X))
    let r : Retract X P.X.obj :=
      { i := rK.i.f
        r := rK.r.f
        retract := by
          have h := congrArg Karoubi.Hom.f rK.retract
          exact h }
    exact ObjectProperty.prop_retractClosure P.X.property r

instance finiteCellKaroubiFunctorCommShift (S : Set D) :
    (finiteCellKaroubiFunctor A D S).CommShift ℤ :=
  karoubiExtension_commShift (derivedFiniteCellInclusion A D S)

instance finiteCellKaroubiFunctorFacCommShift (S : Set D) :
    NatTrans.CommShift (finiteCellKaroubiFunctor_fac A D S).hom ℤ :=
  karoubiExtensionFactors_commShift (derivedFiniteCellInclusion A D S)

lemma modulePerfect_iff_karoubi_essImage (X : DerivedModuleCategory A D) :
    modulePerfect A D X ↔ (finiteCellKaroubiFunctor A D Set.univ).essImage
      ((toKaroubi (DerivedModuleCategory A D)).obj X) :=
  modulePerfectOver_iff_karoubi_essImage A D Set.univ X

end SerrePositivity.DifferentialGraded
