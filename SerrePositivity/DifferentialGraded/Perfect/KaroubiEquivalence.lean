module
public import SerrePositivity.DifferentialGraded.Derived.IdempotentComplete
public import SerrePositivity.DifferentialGraded.Perfect.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # finite cellのKaroubi包絡と指定導来圏内のPerfとの三角同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleDerivedKaroubiEquivalence :
    DerivedModuleCategory A D ≌ Karoubi (DerivedModuleCategory A D) :=
  toKaroubiEquivalence _

instance moduleDerivedKaroubiEquivalenceFunctorCommShift :
    (moduleDerivedKaroubiEquivalence A D).functor.CommShift ℤ := by
  change (toKaroubi (DerivedModuleCategory A D)).CommShift ℤ
  infer_instance

instance moduleDerivedKaroubiEquivalenceInverseCommShift :
    (moduleDerivedKaroubiEquivalence A D).inverse.CommShift ℤ :=
  (moduleDerivedKaroubiEquivalence A D).commShiftInverse ℤ

instance moduleDerivedKaroubiEquivalenceCommShift :
    (moduleDerivedKaroubiEquivalence A D).CommShift ℤ :=
  (moduleDerivedKaroubiEquivalence A D).commShift_of_functor ℤ

instance moduleDerivedKaroubiEquivalenceIsTriangulated :
    (moduleDerivedKaroubiEquivalence A D).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (by
    change (toKaroubi (DerivedModuleCategory A D)).IsTriangulated
    infer_instance)

/-- 形式的な有限cell直和因子を、主導来圏の実際の対象として実現する。 -/
def finiteCellKaroubiRealization (S : Set D) :
    Karoubi (DerivedFiniteCellCategoryOver A D S) ⥤ DerivedModuleCategory A D :=
  finiteCellKaroubiFunctor A D S ⋙ (moduleDerivedKaroubiEquivalence A D).inverse

instance finiteCellKaroubiRealizationFull (S : Set D) :
    (finiteCellKaroubiRealization A D S).Full := by
  dsimp [finiteCellKaroubiRealization]
  infer_instance

instance finiteCellKaroubiRealizationFaithful (S : Set D) :
    (finiteCellKaroubiRealization A D S).Faithful := by
  dsimp [finiteCellKaroubiRealization]
  infer_instance

instance finiteCellKaroubiRealizationCommShift (S : Set D) :
    (finiteCellKaroubiRealization A D S).CommShift ℤ := by
  dsimp [finiteCellKaroubiRealization]
  infer_instance

instance finiteCellKaroubiRealizationIsTriangulated (S : Set D) :
    (finiteCellKaroubiRealization A D S).IsTriangulated := by
  dsimp [finiteCellKaroubiRealization]
  infer_instance

def finiteCellKaroubiRealizationToKaroubiIso (S : Set D) :
    finiteCellKaroubiRealization A D S ⋙ toKaroubi (DerivedModuleCategory A D) ≅
      finiteCellKaroubiFunctor A D S :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (finiteCellKaroubiFunctor A D S)
      (moduleDerivedKaroubiEquivalence A D).counitIso ≪≫ Functor.rightUnitor _

instance finiteCellKaroubiRealizationToKaroubiIsoCommShift (S : Set D) :
    NatTrans.CommShift (finiteCellKaroubiRealizationToKaroubiIso A D S).hom ℤ := by
  dsimp [finiteCellKaroubiRealizationToKaroubiIso]
  infer_instance

/-- 実現は、元のfinite cell上では既存の導来圏への包含に一致する。 -/
def finiteCellKaroubiRealization_fac (S : Set D) :
    toKaroubi (DerivedFiniteCellCategoryOver A D S) ⋙ finiteCellKaroubiRealization A D S ≅
      derivedFiniteCellInclusion A D S :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (finiteCellKaroubiFunctor_fac A D S)
      (moduleDerivedKaroubiEquivalence A D).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (derivedFiniteCellInclusion A D S)
      (moduleDerivedKaroubiEquivalence A D).unitIso.symm ≪≫ Functor.rightUnitor _

instance finiteCellKaroubiRealizationFacCommShift (S : Set D) :
    NatTrans.CommShift (finiteCellKaroubiRealization_fac A D S).hom ℤ := by
  dsimp [finiteCellKaroubiRealization_fac]
  infer_instance

lemma finiteCellKaroubiRealization_perfect (S : Set D)
    (P : Karoubi (DerivedFiniteCellCategoryOver A D S)) :
    modulePerfectOver A D S ((finiteCellKaroubiRealization A D S).obj P) := by
  rw [modulePerfectOver_iff_karoubi_essImage]
  exact ⟨P, ⟨((finiteCellKaroubiRealizationToKaroubiIso A D S).app P).symm⟩⟩

def finiteCellKaroubiToPerfect (S : Set D) :
    Karoubi (DerivedFiniteCellCategoryOver A D S) ⥤ PerfectModuleCategoryOver A D S :=
  (modulePerfectOver A D S).lift (finiteCellKaroubiRealization A D S)
    (finiteCellKaroubiRealization_perfect A D S)

instance finiteCellKaroubiToPerfectFull (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).Full := by
  dsimp [finiteCellKaroubiToPerfect]
  infer_instance

instance finiteCellKaroubiToPerfectFaithful (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).Faithful := by
  dsimp [finiteCellKaroubiToPerfect]
  infer_instance

instance finiteCellKaroubiToPerfectEssSurj (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).EssSurj where
  mem_essImage X := by
    obtain ⟨P, ⟨e⟩⟩ := (modulePerfectOver_iff_karoubi_essImage A D S X.obj).mp X.property
    refine ⟨P, ⟨(modulePerfectOver A D S).isoMk ?_⟩⟩
    exact (moduleDerivedKaroubiEquivalence A D).inverse.mapIso e ≪≫
      ((moduleDerivedKaroubiEquivalence A D).unitIso.app X.obj).symm

instance finiteCellKaroubiToPerfectIsEquivalence (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).IsEquivalence where

instance finiteCellKaroubiToPerfectCommShift (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).CommShift ℤ := by
  dsimp [finiteCellKaroubiToPerfect]
  infer_instance

instance finiteCellKaroubiToPerfectIsTriangulated (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).IsTriangulated := by
  dsimp [finiteCellKaroubiToPerfect]
  infer_instance

def finiteCellKaroubiToPerfectCompInclusion (S : Set D) :
    finiteCellKaroubiToPerfect A D S ⋙ perfectModuleInclusion A D S ≅
      finiteCellKaroubiRealization A D S :=
  (modulePerfectOver A D S).liftCompιIso _ _

instance finiteCellKaroubiToPerfectCompInclusionCommShift (S : Set D) :
    NatTrans.CommShift (finiteCellKaroubiToPerfectCompInclusion A D S).hom ℤ := by
  dsimp [finiteCellKaroubiToPerfectCompInclusion]
  infer_instance

/-- 実際の導来対象としてのPerfとfinite cellのKaroubi包絡との同値。 -/
def finiteCellKaroubiPerfectEquivalence (S : Set D) :
    Karoubi (DerivedFiniteCellCategoryOver A D S) ≌ PerfectModuleCategoryOver A D S :=
  (finiteCellKaroubiToPerfect A D S).asEquivalence

instance finiteCellKaroubiPerfectEquivalenceFunctorCommShift (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).functor.CommShift ℤ := by
  change (finiteCellKaroubiToPerfect A D S).CommShift ℤ
  infer_instance

instance finiteCellKaroubiPerfectEquivalenceInverseCommShift (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).inverse.CommShift ℤ :=
  (finiteCellKaroubiPerfectEquivalence A D S).commShiftInverse ℤ

instance finiteCellKaroubiPerfectEquivalenceCommShift (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).CommShift ℤ :=
  (finiteCellKaroubiPerfectEquivalence A D S).commShift_of_functor ℤ

instance finiteCellKaroubiPerfectEquivalenceIsTriangulated (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (by
    change (finiteCellKaroubiToPerfect A D S).IsTriangulated
    infer_instance)

instance perfectModuleCategoryOverIsIdempotentComplete (S : Set D) :
    IsIdempotentComplete (PerfectModuleCategoryOver A D S) :=
  Idempotents.Equivalence.isIdempotentComplete
    (finiteCellKaroubiPerfectEquivalence A D S) inferInstance

end SerrePositivity.DifferentialGraded
