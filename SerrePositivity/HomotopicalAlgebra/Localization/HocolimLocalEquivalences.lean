module

public import SerrePositivity.HomotopicalAlgebra.Localization.HocolimMappingTests
public import SerrePositivity.HomotopicalAlgebra.Localization.SmallHomTests

/-! # Local equivalences are preserved by actual homotopy colimits

The source-natural RMap formula reduces this to homotopy invariance of the
actual simplicial holim functor. No localized model structure is used.
-/

@[expose] public section
universe w v u vD uD vT uT
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.DiagramModel

namespace SerrePositivity.Bousfield.LocalizedSourceTransfer
variable {D : Type uD} [Category.{vD} D] {T : Type uT} [Category.{vT} T]
  [ModelCategory SSet.{w}]

/-- An ordinary localized natural isomorphism transfers source mapping tests. -/
lemma map_weakEquivalence (F G : D ⥤ T ⥤ SSet.{w})
    (e : F ⋙ (Functor.whiskeringRight T SSet.{w} (weakEquivalences SSet.{w}).Localization).obj
        (weakEquivalences SSet.{w}).Q ≅
      G ⋙ (Functor.whiskeringRight T SSet.{w} (weakEquivalences SSet.{w}).Localization).obj
        (weakEquivalences SSet.{w}).Q)
    {d d' : D} (a : d ⟶ d') (Y : T)
    (ha : weakEquivalences SSet.{w} ((G.map a).app Y)) :
    weakEquivalences SSet.{w} ((F.map a).app Y) := by
  let L := (weakEquivalences SSet.{w}).Q
  have : IsIso (L.map ((G.map a).app Y)) :=
    Localization.inverts L (weakEquivalences SSet.{w}) _ ha
  have hn := congrArg (fun t => t.app Y) (e.hom.naturality a)
  change L.map ((F.map a).app Y) ≫ ((e.app d').app Y).hom =
    ((e.app d).app Y).hom ≫ L.map ((G.map a).app Y) at hn
  apply (Quillen.weakEquivalences_iff_isIso_map L _).mpr
  apply (isIso_comp_right_iff _ ((e.app d').app Y).hom).mp
  rw [hn]
  infer_instance

end SerrePositivity.Bousfield.LocalizedSourceTransfer

namespace SerrePositivity.Bousfield.HocolimSourceTests
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

include IS JS hcof hfib hw in
lemma map_source_at_hocolim_weakEquivalence {D E : K ⥤ C} (a : D ⟶ E) (Y : C)
    (ha : ∀ k, weakEquivalences SSet.{w}
      (((SmallHomComparison.chosenHom cof fib).map (a.app k).op).app Y)) :
    weakEquivalences SSet.{w} (((SmallHomComparison.chosenHom cof fib).map
      ((HomotopyColimit.functor K I J).map a).op).app Y) := by
  have := SimplicialModel.simplicial_isQuillenBifunctor hcof hfib
  have ht : weakEquivalences SSet.{w}
      (((HocolimRMapFormula.target K IS JS cof fib).map a.op).app Y) :=
    HomotopyLimit.map_weakEquivalence Kᵒᵖ IS JS
      (((SmallPointwiseMappingComparison.pointwiseRMap K cof fib).map a.op).app Y)
      (fun k => ha k.unop)
  exact LocalizedSourceTransfer.map_weakEquivalence
    (HocolimRMapFormula.source K I J cof fib) (HocolimRMapFormula.target K IS JS cof fib)
    (HocolimRMapFormula.localizedIso K I J IS JS cof fib hcof hfib hw
      (weakEquivalences SSet.{w}).Q) a.op Y ht

include IS JS hcof hfib hw in
lemma smallLocalEquivalence_hocolim (S : MorphismProperty C) {D E : K ⥤ C} (a : D ⟶ E)
    (ha : ∀ k, smallLocalEquivalences.{w, v, u} cof fib S (a.app k)) :
    smallLocalEquivalences.{w, v, u} cof fib S ((HomotopyColimit.functor K I J).map a) := by
  intro Y hY
  exact map_source_at_hocolim_weakEquivalence K I J IS JS cof fib hcof hfib hw a Y
    (fun k => ha k Y hY)

variable [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

include IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
/-- The original local-equivalence class, without identifying its Hom universe with w. -/
lemma localEquivalence_hocolim (S : MorphismProperty C) {D E : K ⥤ C} (a : D ⟶ E)
    (ha : ∀ k, localEquivalences.{v, u} cof fib S (a.app k)) :
    localEquivalences.{v, u} cof fib S ((HomotopyColimit.functor K I J).map a) := by
  have he := smallLocalEquivalences_eq.{w, v, u} cof fib hcof hfib hcofV hfibV hcofB hfibB S
  rw [← he] at ha ⊢
  exact smallLocalEquivalence_hocolim K I J IS JS cof fib hcof hfib hw S a ha

include IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
/-- Actual weak hocolim comparisons transfer the result to the ordinary colimit. -/
lemma localEquivalence_colim_of_weakComparisons (S : MorphismProperty C)
    {D E : K ⥤ C} (a : D ⟶ E)
    (ha : ∀ k, localEquivalences.{v, u} cof fib S (a.app k))
    (hD : weakEquivalences C ((HomotopyColimit.comparison K I J).app D))
    (hE : weakEquivalences C ((HomotopyColimit.comparison K I J).app E)) :
    localEquivalences.{v, u} cof fib S ((colim : (K ⥤ C) ⥤ C).map a) := by
  have h := localEquivalence_hocolim K I J IS JS cof fib hcof hfib hw
    hcofV hfibV hcofB hfibB S a ha
  have hcD := weakEquivalences_le_localEquivalences cof fib hcofV S _ hD
  have hcE := weakEquivalences_le_localEquivalences cof fib hcofV S _ hE
  have hn := (HomotopyColimit.comparison K I J).naturality a
  exact (localEquivalences cof fib S).of_precomp _ _ hcD
    (hn ▸ (localEquivalences cof fib S).comp_mem _ _ h hcE)

include IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localEquivalence_colim_of_projectiveCofibrant (S : MorphismProperty C)
    {D E : K ⥤ C} (a : D ⟶ E)
    (ha : ∀ k, localEquivalences.{v, u} cof fib S (a.app k))
    (hD : let := Projective.modelCategory K I J; IsCofibrant D)
    (hE : let := Projective.modelCategory K I J; IsCofibrant E) :
    localEquivalences.{v, u} cof fib S ((colim : (K ⥤ C) ⥤ C).map a) :=
  localEquivalence_colim_of_weakComparisons K I J IS JS cof fib hcof hfib hw
    hcofV hfibV hcofB hfibB S a ha
    (HomotopyColimit.comparison_weakEquivalence_of_cofibrant K I J D hD)
    (HomotopyColimit.comparison_weakEquivalence_of_cofibrant K I J E hE)

end SerrePositivity.Bousfield.HocolimSourceTests
