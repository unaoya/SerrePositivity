module
public import SerrePositivity.DifferentialGraded.Endomorphism.EssentialImageRetracts

/-! # 再構成比較の本質的像の整数shift閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

lemma perfectEndomorphismEssentialImage_shift
    {Y : DerivedModuleCategory A (EndomorphismObject E.val)}
    (hY : (perfectEndomorphismHomToDerived A D S E).essImage Y) (s : ℤ) :
    (perfectEndomorphismHomToDerived A D S E).essImage (Y⟦s⟧) := by
  obtain ⟨X, ⟨e⟩⟩ := hY
  let M := X.obj.as.obj
  have hM : modulePerfectOver A D S ((moduleToDerived A D).obj M) := X.property
  let Xs : PerfectModuleCategoryOver A D S :=
    ⟨(moduleToDerived A D).obj (M⟦s⟧), (modulePerfectOver A D S).prop_of_iso
      (((moduleToDerived A D).commShiftIso s).app M).symm
      ((modulePerfectOver A D S).le_shift s _ hM)⟩
  refine ⟨Xs, ⟨?_⟩⟩
  exact endomorphismDerivedHomComputation A D E.val E.property.1 (M⟦s⟧) ≪≫
    (moduleToDerived A (EndomorphismObject E.val)).mapIso
      (dgModuleFunctorShiftIso A (EndomorphismObject E.val) D
        (endomorphismModuleHom A D E.val) s (ForgetEnrichment.to (Complex A) M)) ≪≫
    ((moduleToDerived A (EndomorphismObject E.val)).commShiftIso s).app
      ((endomorphismModuleHom A D E.val).onClosed.obj M) ≪≫
    (shiftFunctor (DerivedModuleCategory A (EndomorphismObject E.val)) s).mapIso
      ((endomorphismDerivedHomComputation A D E.val E.property.1 M).symm ≪≫ e)

instance perfectEndomorphismEssentialImageStableUnderShift :
    (perfectEndomorphismHomToDerived A D S E).essImage.IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun _ hY => perfectEndomorphismEssentialImage_shift A D S E hY s⟩

end SerrePositivity.DifferentialGraded
