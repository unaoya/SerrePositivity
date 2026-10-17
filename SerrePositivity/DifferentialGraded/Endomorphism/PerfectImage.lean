module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleShiftImage
public import SerrePositivity.DifferentialGraded.Endomorphism.ThickHomComparison

/-! # 指定対象のthick閉包のdg像はperfectに入る -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) (B : Type w)
  [DGCategory A D] [DGCategory A B] [Small.{u} D] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

def dgModuleFunctorDerivedImageComputation (M : ModuleCategory A D) :
    (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B).obj ((moduleToHomotopy A D).obj M) ≅
      (moduleToDerived A B).obj (F.onClosed.obj M) :=
  (moduleToHomotopyDerivedIso A B).app (F.onClosed.obj M)

def dgModuleFunctorDerivedImageShiftIso (s : ℤ) (X : ModuleHomotopyCategory A D) :
    (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B).obj (X⟦s⟧) ≅
      ((F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B).obj X)⟦s⟧ :=
  (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B).mapIso
      (((moduleToHomotopy A D).commShiftIso s).app X.as).symm ≪≫
    dgModuleFunctorDerivedImageComputation A D B F (X.as⟦s⟧) ≪≫
    (moduleToDerived A B).mapIso
      (dgModuleFunctorShiftIso A B D F s (ForgetEnrichment.to (Complex A) X.as)) ≪≫
    ((moduleToDerived A B).commShiftIso s).app (F.onClosed.obj X.as) ≪≫
    (shiftFunctor (DerivedModuleCategory A B) s).mapIso
      (dgModuleFunctorDerivedImageComputation A D B F X.as).symm

/-- 主Kから主導来圏へ送ったdg像がperfectである、という始域上の性質。 -/
def dgModuleFunctorPerfectLocus : ObjectProperty (ModuleHomotopyCategory A D) :=
  (modulePerfect A B).inverseImage (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B)

instance dgModuleFunctorPerfectLocusStableUnderRetracts :
    (dgModuleFunctorPerfectLocus A D B F).IsStableUnderRetracts where
  of_retract a hY := (modulePerfect A B).prop_of_retract
    (a.map (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B)) hY

instance dgModuleFunctorPerfectLocusStableUnderShift :
    (dgModuleFunctorPerfectLocus A D B F).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun X hX =>
    (modulePerfect A B).prop_of_iso (dgModuleFunctorDerivedImageShiftIso A D B F s X).symm
      ((modulePerfect A B).le_shift s _ hX)⟩

lemma dgModuleFunctorPerfectLocus_triangle_obj₃
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ distTriang _)
    (h₁ : dgModuleFunctorPerfectLocus A D B F T.obj₁)
    (h₂ : dgModuleFunctorPerfectLocus A D B F T.obj₂) :
    dgModuleFunctorPerfectLocus A D B F T.obj₃ := by
  let H := F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  have hM := (modulePerfect A B).prop_of_iso
    (H.mapIso (Triangle.π₁.mapIso e) ≪≫ dgModuleFunctorDerivedImageComputation A D B F M) h₁
  have hN := (modulePerfect A B).prop_of_iso
    (H.mapIso (Triangle.π₂.mapIso e) ≪≫ dgModuleFunctorDerivedImageComputation A D B F N) h₂
  have hc := (modulePerfect A B).ext_of_isTriangulatedClosed₃'
    (moduleDerivedConeTriangle A B (F.onClosed.map f))
    (moduleDerivedConeTriangle_distinguished A B (F.onClosed.map f)) hM hN
  rw [ObjectProperty.isoClosure_eq_self] at hc
  exact (modulePerfect A B).prop_of_iso
    ((moduleToDerived A B).mapIso (dgModuleFunctorConeIso A D B F f) ≪≫
      (dgModuleFunctorDerivedImageComputation A D B F (moduleCone A D f)).symm ≪≫
      H.mapIso (Triangle.π₃.mapIso e.symm)) hc

instance dgModuleFunctorPerfectLocusTriangulatedClosed₃ :
    (dgModuleFunctorPerfectLocus A D B F).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk'
    (dgModuleFunctorPerfectLocus_triangle_obj₃ A D B F)

instance dgModuleFunctorPerfectLocusTriangulatedClosed₂ :
    (dgModuleFunctorPerfectLocus A D B F).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

lemma dgModuleFunctor_thick_perfect (E : RightModule A D)
    (hE : modulePerfect A B ((moduleToDerived A B).obj
      (F.onClosed.obj (ForgetEnrichment.of (Complex A) E))))
    {M : ModuleCategory A D}
    (hM : endomorphismThickClosure A D E ((moduleToHomotopy A D).obj M)) :
    modulePerfect A B ((moduleToDerived A B).obj (F.onClosed.obj M)) := by
  let P := dgModuleFunctorPerfectLocus A D B F
  have hEP : P ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) E)) :=
    (modulePerfect A B).prop_of_iso
      (dgModuleFunctorDerivedImageComputation A D B F (ForgetEnrichment.of (Complex A) E)).symm hE
  have : P.Nonempty := ObjectProperty.nonempty_of_prop hEP
  have : P.ContainsZero := inferInstance
  have : P.IsTriangulated := ⟨⟩
  exact (modulePerfect A B).prop_of_iso (dgModuleFunctorDerivedImageComputation A D B F M)
    (endomorphismThickClosure_le A D E P hEP _ hM)

variable (E : RightModule A D)

lemma endomorphismHom_thick_perfect {M : ModuleCategory A D}
    (hM : endomorphismThickClosure A D E ((moduleToHomotopy A D).obj M)) :
    modulePerfect A (EndomorphismObject E)
      ((moduleToDerived A (EndomorphismObject E)).obj
        ((endomorphismModuleHom A D E).onClosed.obj M)) := by
  apply dgModuleFunctor_thick_perfect A D (EndomorphismObject E)
    (endomorphismModuleHom A D E) E _ hM
  exact (modulePerfect A (EndomorphismObject E)).prop_of_iso
    ((moduleToDerived A (EndomorphismObject E)).mapIso (endomorphismRegularModuleIso A D E))
    (modulePerfectOver_representable A (EndomorphismObject E) .point (Set.mem_univ _))

lemma perfectEndomorphismHom_obj_perfect (S : Set D) (E : PerfectDGModuleOver A D S)
    (hgen : endomorphismThickGeneratesPerfect A D S E) (M : PerfectDGModuleOver A D S) :
    modulePerfect A (EndomorphismObject E.val)
      ((moduleToDerived A (EndomorphismObject E.val)).obj
        (ForgetEnrichment.of (Complex A) ((perfectEndomorphismModuleHom A D S E).obj M))) :=
  endomorphismHom_thick_perfect A D E.val (hgen M)

lemma perfectEndomorphismDerivedHom_obj_perfect (S : Set D) (E : PerfectDGModuleOver A D S)
    (hgen : endomorphismThickGeneratesPerfect A D S E) (X : PerfectModuleCategoryOver A D S) :
    modulePerfect A (EndomorphismObject E.val)
      ((endomorphismDerivedHom A D E.val E.property.1).obj X.obj) := by
  let R := moduleCanonicalProjectiveResolution A D X.obj.as.obj
  let e : (moduleToDerived A D).obj R.obj ≅ X.obj := moduleDerivedIso A D R.π R.quasiIso
  let M : PerfectDGModuleOver A D S :=
    ⟨ForgetEnrichment.to (Complex A) R.obj, R.projective,
      (modulePerfectOver A D S).prop_of_iso e.symm X.property⟩
  exact (modulePerfect A (EndomorphismObject E.val)).prop_of_iso
    ((endomorphismDerivedHomComputation A D E.val E.property.1 R.obj).symm ≪≫
      (endomorphismDerivedHom A D E.val E.property.1).mapIso e)
    (perfectEndomorphismHom_obj_perfect A D S E hgen M)

/-- 主導来Hom関手の、主Perfから主Perfへの実際の制限。 -/
def perfectEndomorphismHomToPerfect (S : Set D) (E : PerfectDGModuleOver A D S)
    (hgen : endomorphismThickGeneratesPerfect A D S E) :
    PerfectModuleCategoryOver A D S ⥤ PerfectModuleCategory A (EndomorphismObject E.val) :=
  (modulePerfect A (EndomorphismObject E.val)).lift
    (perfectModuleInclusion A D S ⋙ endomorphismDerivedHom A D E.val E.property.1)
    (perfectEndomorphismDerivedHom_obj_perfect A D S E hgen)

end SerrePositivity.DifferentialGraded
