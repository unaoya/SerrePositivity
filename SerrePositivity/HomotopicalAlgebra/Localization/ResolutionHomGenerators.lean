module

public import SerrePositivity.HomotopicalAlgebra.Localization.HomotopyGenerators
public import SerrePositivity.HomotopicalAlgebra.Localization.FrameTargetTests

/-! # Small cofibrant generators detected by actual resolution Hom

The small-Hom generating family is transported to the original Hom universe.
For fibrant endpoints the target replacement is removed by its actual unit.
The resulting family is independent of both specified factorizations.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy

namespace SerrePositivity.Bousfield.HomotopyGenerators
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include I J IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw in
lemma exists_small_cofibrant_resolution_generators :
    ∃ (ι : Type w) (G : ι → C), (∀ i, IsCofibrant (G i)) ∧
      ∀ (cof : MorphismProperty.FunctorialFactorizationData
          (cofibrations C) (trivialFibrations C))
        {Y Z : C}
        [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z),
        weakEquivalences C f ↔ ∀ i, weakEquivalences SSet.{v}
          ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((cosimplicialResolutionFamily cof).obj.obj (G i))).map f) := by
  obtain ⟨κ, hκ, ι, G, hc, hp, hd⟩ := exists_small_presentable_cofibrant_generators
    hcofW hfibW hcofV hfibV hcofM hfibM I J IS JS hw
  refine ⟨ι, G, hc, ?_⟩
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration I J
  let fib := MorphismProperty.functorialFactorizationData (trivialCofibrations C) (fibrations C)
  intro cof Y Z _ _ f
  have ht (i : ι) :
      weakEquivalences SSet.{w}
        (((SmallHomComparison.chosenHom cof fib).obj (Opposite.op (G i))).map f) ↔
      weakEquivalences SSet.{v}
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((cosimplicialResolutionFamily cof).obj.obj (G i))).map f) := by
    have hu := SimplicialModel.UniverseLift.weakEquivalences_iff_of_liftedArrowIso.{v,w}
      hcofW hfibW hcofM hfibM hcofV hfibV _ _
      (SmallHomComparison.targetArrowIso (cosimplicialResolutionFamily cof).obj
        (fibrantTarget fib) (Opposite.op (G i)) f)
    exact hu.trans (FrameTargetTests.chosenResolutionHom_map_iff fib hcofV hfibV cof (G i) f)
  constructor
  · intro hf i
    exact (ht i).mp ((hd cof fib f).mp hf i)
  · intro hf
    exact (hd cof fib f).mpr (fun i ↦ (ht i).mpr (hf i))

end SerrePositivity.Bousfield.HomotopyGenerators
