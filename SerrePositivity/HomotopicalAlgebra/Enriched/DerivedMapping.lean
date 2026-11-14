module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Enriched.TensorCotensor
public import SerrePositivity.HomotopicalAlgebra.Monoidal.PullbackHomSource
public import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison
public import SerrePositivity.HomotopicalAlgebra.Localization.MappingTests

/-! # Actual V-valued derived Hom and its local tests

The bifunctor is the existing enriched Hom evaluated at the specified
cofibrant and fibrant replacements. It is V-valued, separately from the
ordinary simplicial RMap used by the localization existence theorem.
The tensor model axiom proves fibrancy and invariance in both variables.
-/

@[expose] public section
universe vV uV vC uC
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Enriched
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [ModelCategory V]
  {C : Type uC} [Category.{vC} C] [ModelCategory C] [EnrichedOrdinaryCategory V C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

def derivedHom : Cᵒᵖ ⥤ C ⥤ V :=
  (cofibrantSource cof).op ⋙ eHomFunctor V C ⋙
    (Functor.whiskeringLeft C C V).obj (fibrantTarget fib)

abbrev localObjects (S : MorphismProperty C) : C → Prop :=
  Bousfield.MappingTests.localObjects (derivedHom (V := V) cof fib) (weakEquivalences V) S

abbrev localEquivalences (S : MorphismProperty C) : MorphismProperty C :=
  Bousfield.MappingTests.localEquivalences (derivedHom (V := V) cof fib) (weakEquivalences V) S

variable (P : TensorCotensor V C) [Quillen.IsQuillenBifunctor P.tensor]

include P in
lemma source_weakEquivalence {X Z : C} [IsCofibrant X] [IsCofibrant Z]
    (f : X ⟶ Z) (hf : weakEquivalences C f) (Y : C) [IsFibrant Y] :
    weakEquivalences V (((eHomFunctor V C).map f.op).app Y) := by
  have := (tensor_iff_mapping_model P).mp inferInstance
  exact Quillen.pullbackHom_source_weakEquivalence P.tensorHom f hf Y

include P in
lemma mapping_isFibrant (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    IsFibrant (((eHomFunctor V C).obj (Opposite.op X)).obj Y) := by
  have : ((eHomFunctor V C).obj (Opposite.op X)).IsRightAdjoint :=
    (P.tensorHom.adj X).isRightAdjoint
  have := mapping_isRightQuillen P X
  exact Quillen.isFibrant_obj _ Y

include P in
lemma derivedHom_isFibrant (X : Cᵒᵖ) (Y : C) :
    IsFibrant (((derivedHom (V := V) cof fib).obj X).obj Y) := by
  have := cofibrantSource_isCofibrant cof X.unop
  have := fibrantTarget_isFibrant fib Y
  exact mapping_isFibrant P _ _

include P in
lemma derivedHom_source_weakEquivalence {X Z : C} (f : X ⟶ Z)
    (hf : weakEquivalences C f) (Y : C) :
    weakEquivalences V (((derivedHom (V := V) cof fib).map f.op).app Y) := by
  let Q := cofibrantSource cof
  let q := cofibrantSourceComparison cof
  have hX := (cofibrantSourceComparison_trivialFibration cof X).2
  have hZ := (cofibrantSourceComparison_trivialFibration cof Z).2
  have hQ : weakEquivalences C (Q.map f) := (weakEquivalences C).of_postcomp _ _ hZ
    ((q.naturality f).symm ▸ (weakEquivalences C).comp_mem _ _ hX hf)
  have := cofibrantSource_isCofibrant cof X
  have := cofibrantSource_isCofibrant cof Z
  have := fibrantTarget_isFibrant fib Y
  exact source_weakEquivalence P (Q.map f) hQ _

include P in
lemma derivedHom_target_weakEquivalence (X : Cᵒᵖ) {Y Z : C} (f : Y ⟶ Z)
    (hf : weakEquivalences C f) :
    weakEquivalences V (((derivedHom (V := V) cof fib).obj X).map f) := by
  have := cofibrantSource_isCofibrant cof X.unop
  have := fibrantTarget_isFibrant fib Y
  have := fibrantTarget_isFibrant fib Z
  have := mapping_isRightQuillen P ((cofibrantSource cof).obj X.unop)
  have : WeakEquivalence ((fibrantTarget fib).map f) := ⟨fibrantTarget_map_weakEquivalence fib f hf⟩
  exact (weakEquivalence_iff _).mp
    (Quillen.map_weakEquivalence_of_fibrant ((eHomFunctor V C).obj
      (Opposite.op ((cofibrantSource cof).obj X.unop))) ((fibrantTarget fib).map f))

end SerrePositivity.Enriched

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.3.1.8" (partial := component) "仮定：TensorCotensor SSet C と Quillen compatibility、ModelCategory SSet が標準 horn-RLP を fibrations とする（証明済み具体的 instance なし）。結論：X cofibrant,Y fibrant なら元の enriched mapping object は fibrant、標準 fibrations の下では Kan になるという最初の成分に一致。π0 Map(X,Y) と同じ hC の Hom の指定全単射はこの型に含まない。"] _root_.SerrePositivity.Enriched.mapping_isFibrant
