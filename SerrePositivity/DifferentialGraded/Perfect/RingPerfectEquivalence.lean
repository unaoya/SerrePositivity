module
public import SerrePositivity.DifferentialGraded.Perfect.RingPerfectRepresentatives
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementIdempotents
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 既存PerfectHomotopyと一対象主Perfの同値、およびホモトピー冪等分裂

元の比較関手に本質的全射性を証明する。Karoubi包絡による置換は行わない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]
local instance : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

def ringStrictPerfectHomotopyDerivedIso (K : Complex A) (hK : strictlyPerfectComplex A K) :
    (perfectHomotopyToDGDerived A).obj (perfectHomotopyObj A K hK) ≅
      (moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj K) :=
  (perfectHomotopyToDGDerivedCanonicalIso A).app (perfectHomotopyObj A K hK) ≪≫
    (ringDerivedEquivalence A).inverse.mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app K) ≪≫
        ringComplexDerivedUnitIso A K

instance perfectHomotopyToDGPerfectEssSurj : (perfectHomotopyToDGPerfect A).EssSurj where
  mem_essImage X := by
    obtain ⟨K, hK, ⟨eK⟩⟩ := modulePerfect_ring_has_strictlyPerfectRepresentative A X.property
    let P := perfectHomotopyObj A K hK
    refine ⟨P, ⟨(modulePerfect A PUnit.{1}).isoMk ?_⟩⟩
    exact (perfectHomotopyToDGPerfectCompInclusion A).app P ≪≫
      ringStrictPerfectHomotopyDerivedIso A K hK ≪≫ eK

instance perfectHomotopyToDGPerfectIsEquivalence :
    (perfectHomotopyToDGPerfect A).IsEquivalence where

def ringPerfectHomotopyEquivalence : PerfectHomotopy A ≌ PerfectModuleCategory A PUnit.{1} :=
  (perfectHomotopyToDGPerfect A).asEquivalence

lemma ringPerfectHomotopyEquivalence_functor :
    (ringPerfectHomotopyEquivalence A).functor = perfectHomotopyToDGPerfect A := rfl

instance ringPerfectHomotopyEquivalenceFunctorLinear :
    (ringPerfectHomotopyEquivalence A).functor.Linear A :=
  inferInstanceAs ((perfectHomotopyToDGPerfect A).Linear A)

instance ringPerfectHomotopyEquivalenceInverseLinear :
    (ringPerfectHomotopyEquivalence A).inverse.Linear A := inferInstance

instance ringPerfectHomotopyEquivalenceFunctorCommShift :
    (ringPerfectHomotopyEquivalence A).functor.CommShift ℤ :=
  inferInstanceAs ((perfectHomotopyToDGPerfect A).CommShift ℤ)

instance ringPerfectHomotopyEquivalenceInverseCommShift :
    (ringPerfectHomotopyEquivalence A).inverse.CommShift ℤ :=
  (ringPerfectHomotopyEquivalence A).commShiftInverse ℤ

instance ringPerfectHomotopyEquivalenceCommShift :
    (ringPerfectHomotopyEquivalence A).CommShift ℤ :=
  (ringPerfectHomotopyEquivalence A).commShift_of_functor ℤ

instance ringPerfectHomotopyEquivalenceIsTriangulated :
    (ringPerfectHomotopyEquivalence A).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _
    (inferInstanceAs ((perfectHomotopyToDGPerfect A).IsTriangulated))

instance perfectHomotopyIsIdempotentComplete : IsIdempotentComplete (PerfectHomotopy A) :=
  Idempotents.Equivalence.isIdempotentComplete (ringPerfectHomotopyEquivalence A).symm inferInstance

lemma perfectHomotopy_idempotent_splits_complex (X : PerfectHomotopy A) (p : X ⟶ X)
    (hp : p ≫ p = p) :
    ∃ (K : Complex A) (hK : strictlyPerfectComplex A K)
      (i : perfectHomotopyObj A K hK ⟶ X) (r : X ⟶ perfectHomotopyObj A K hK),
      i ≫ r = 𝟙 _ ∧ r ≫ i = p := by
  obtain ⟨Y, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split X p hp
  let K : Complex A := Y.obj.as
  have hK : strictlyPerfectComplex A K := (perfectHomotopyProperty_quotient A K).1 Y.property
  exact ⟨K, hK, i, r, hir, hri⟩

instance strictPerfectDGComplexToDGPerfectEssSurj :
    (strictPerfectDGComplexToDGPerfect A).EssSurj where
  mem_essImage X := by
    obtain ⟨P, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (perfectHomotopyToDGPerfect A) X
    exact ⟨(strictPerfectDGComplexHomotopyEquivalence A).inverse.obj P, ⟨e⟩⟩

instance strictPerfectDGComplexToPerfectDGHomotopyEssSurj :
    (strictPerfectDGComplexToPerfectDG A).onHomotopy.EssSurj := by
  let F := (strictPerfectDGComplexToPerfectDG A).onHomotopy
  let G := perfectDGModuleToPerfect A PUnit.{1} Set.univ
  have : (F ⋙ G).EssSurj := inferInstanceAs ((strictPerfectDGComplexToDGPerfect A).EssSurj)
  exact Functor.essSurj_of_comp_fully_faithful F G

lemma strictPerfectDGComplexToPerfectDG_homQuasiIso :
    HomQuasiIso (strictPerfectDGComplexToPerfectDG A) := by
  intro P K
  change QuasiIso (ringConstantHomIso A P.val K.val).inv
  infer_instance

lemma strictPerfectDGComplexToPerfectDG_quasiEquivalence :
    QuasiEquivalence (strictPerfectDGComplexToPerfectDG A) :=
  ⟨strictPerfectDGComplexToPerfectDG_homQuasiIso A, inferInstance⟩

end SerrePositivity.DifferentialGraded
