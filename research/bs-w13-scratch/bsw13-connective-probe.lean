import SerrePositivity.BhattScholze.Almost.CompletedModuleTensor
import SerrePositivity.InfinityCategories.Derived.SemifreeKProjective

noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Almost
open CategoryTheory InfinityCategories DerivedCompletion
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- A bounded derived vertex and the chosen bounded-above model admit a quasi-isomorphism. -/
private theorem exists_projectiveModelToVertex
    (X : DVertex R)
    (P : BoundedAboveDerivedModel ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨X⟩)) :
    ∃ f : P.complex ⟶ (X.obj 0).val, QuasiIso f := by
  let e := P.iso ≪≫ derivedVertexLocalizationIso X
  obtain ⟨f, hf⟩ := exists_cochainMap_of_isKProjective e.hom
  refine ⟨f, (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) f).mp ?_⟩
  rw [hf]
  infer_instance

/-- The boundedness of the ordinary derived tensor transfers to the actual vertex model. -/
theorem completedModuleTensor_isLE (p : ℕ) (X Y : DVertex R) (i j : ℤ)
    (hX : ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨X⟩).IsLE i)
    (hY : ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨Y⟩).IsLE j) :
    ((derivedInfinityHomotopyEquivalence R).functor.obj
      ⟨completedModuleTensor p R X Y⟩).IsLE (i + j) := by
  let e := derivedInfinityHomotopyEquivalence R
  have := hX
  have := hY
  let P := BoundedAboveDerivedModel.ofIsLE (e.functor.obj ⟨X⟩) i
  let Q := BoundedAboveDerivedModel.ofIsLE (e.functor.obj ⟨Y⟩) j
  obtain ⟨f, hf⟩ := exists_projectiveModelToVertex X P
  obtain ⟨g, hg⟩ := exists_projectiveModelToVertex Y Q
  have := complexSemifree_isKProjective R (X.obj 0).property
  have := complexSemifree_isKProjective R (Y.obj 0).property
  have := cochainTensorMap_quasiIso_of_KProjective f g
  let h := asIso (DerivedCategory.Q.map (cochainTensorMap f g))
  let X' : DerivedCategory.Minus (ModuleCat R) := ⟨_, ⟨i, hX⟩⟩
  let Y' : DerivedCategory.Minus (ModuleCat R) := ⟨_, ⟨j, hY⟩⟩
  have hXY : ((boundedAboveDerivedTensor.obj (X', Y')).obj).IsLE (i + j) :=
    boundedAboveDerivedTensor_isLE_add X' Y' i j
  let hcomp := (derivedComplexCompletionFunctor R (p : R)).mapIso
    (boundedAboveDerivedTensorModelIso X' Y' P Q ≪≫ h)
  have := derivedComplexCompletionFunctor_isLE R (p : R) _ _ hXY
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (hcomp ≪≫ (e.counitIso.app _).symm) (i + j)

#print axioms completedModuleTensor_isLE

end SerrePositivity.BhattScholze.Almost
