module

public import SerrePositivity.HomotopicalAlgebra.Localization.HocolimLocalEquivalences
public import SerrePositivity.HomotopicalAlgebra.Diagram.SpanHomotopyColimit

/-! # Local equivalences on colimits of cofibration spans

The hocolim comparison for one-cofibration spans is an actual original
weak equivalence. Thus the previously proved hocolim formula applies to
the ordinary colimit, without an objectwise cofibrancy assumption.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

section Transfer
variable [ModelCategory SSet.{v}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcofV in
lemma localEquivalence_of_colimit_comparison (K : Type w) [SmallCategory K]
    (S : MorphismProperty C) {D E : K ⥤ C} (a : D ⟶ E)
    (s : Cocone D) (hs : IsColimit s) (t : Cocone E) (ht : IsColimit t)
    (z : s.pt ⟶ t.pt) (hz : ∀ k, s.ι.app k ≫ z = a.app k ≫ t.ι.app k)
    (ha : localEquivalences.{v, u} (C := C) cof fib S ((colim : (K ⥤ C) ⥤ C).map a)) :
    localEquivalences.{v, u} (C := C) cof fib S z := by
  let eS := (colimit.isColimit D).coconePointUniqueUpToIso hs
  let eT := (colimit.isColimit E).coconePointUniqueUpToIso ht
  have hS (k) : colimit.ι D k ≫ eS.hom = s.ι.app k :=
    (colimit.isColimit D).comp_coconePointUniqueUpToIso_hom hs k
  have hT (k) : colimit.ι E k ≫ eT.hom = t.ι.app k :=
    (colimit.isColimit E).comp_coconePointUniqueUpToIso_hom ht k
  have hn : (colim : (K ⥤ C) ⥤ C).map a ≫ eT.hom = eS.hom ≫ z := by
    apply colimit.hom_ext
    intro k
    rw [colimit.ι_map_assoc, hT, ← Category.assoc, hS]
    exact (hz k).symm
  have hS' := weakEquivalences_le_localEquivalences cof fib hcofV S eS.hom
    ((weakEquivalences C).of_isIso eS.hom)
  have hT' := weakEquivalences_le_localEquivalences cof fib hcofV S eT.hom
    ((weakEquivalences C).of_isIso eT.hom)
  exact (localEquivalences.{v, u} (C := C) cof fib S).of_precomp _ _ hS'
    (hn ▸ (localEquivalences.{v, u} (C := C) cof fib S).comp_mem _ _ ha hT')

end Transfer

variable (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)
  [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localEquivalence_span_colim (K : Type w) [SmallCategory K] (e : K ≌ WalkingSpan)
    (S : MorphismProperty C) {D E : K ⥤ C} (a : D ⟶ E)
    (hD : cofibrations C (D.map (e.inverse.map WalkingSpan.Hom.fst)))
    (hE : cofibrations C (E.map (e.inverse.map WalkingSpan.Hom.fst)))
    (ha : ∀ k, localEquivalences.{v, u} (C := C) cof fib S (a.app k)) :
    localEquivalences.{v, u} (C := C) cof fib S ((colim : (K ⥤ C) ⥤ C).map a) :=
  HocolimSourceTests.localEquivalence_colim_of_weakComparisons K I J IS JS cof fib
    hcof hfib hw hcofV hfibV hcofB hfibB S a ha
    (HomotopyColimit.comparison_weakEquivalence_of_span K e I J D hD)
    (HomotopyColimit.comparison_weakEquivalence_of_span K e I J E hE)

end SerrePositivity.Bousfield
