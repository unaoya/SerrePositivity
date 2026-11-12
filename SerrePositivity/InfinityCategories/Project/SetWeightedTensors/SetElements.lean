module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscreteSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTransportComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallStraighteningReconstruction
public import Mathlib.CategoryTheory.Elements

/-!
概要：集合値図式の元の圏の nerve を、その離散空間値図式の unstraightening と底上で比較する。
方針：各射列を、底の射列とその始点の元に分け、simplicial replacement の標準比較を合成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors
variable {I : Type u} [SmallCategory I] (P : I ⥤ Type u)

abbrev spaceDiagram := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan)
abbrev coefficients := (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget

instance coefficientsKan (i : I) : ((coefficients P).obj i).KanComplex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan.obj (P.obj i)).isKanComplex

/-- 元の圏の射列を底の射列と始点でのラベルに分解する。 -/
def elementsToReplacement : nerve P.Elements ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement (coefficients P) where
  app _ := ↾fun s => ⟨s ⋙ Functor.Elements.π P, SSet.const (s.obj 0).val⟩
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro s
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro t
    exact (s.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))).map_val.symm

private def liftChain {n : ℕ} (s : ComposableArrows I n) (a : P.obj (s.obj 0)) :
    ComposableArrows P.Elements n where
  obj i := P.elementsMk (s.obj i) (P.map (s.map (homOfLE (Fin.zero_le i))) a)
  map {i j} f := ⟨s.map f, by rw [← Functor.map_comp_apply, ← s.map_comp]; rfl⟩
  map_id _ := Functor.Elements.Hom.ext (s.map_id _)
  map_comp f g := Functor.Elements.Hom.ext (s.map_comp f g)

private lemma liftChain_recover {n : ℕ} (s : ComposableArrows P.Elements n) :
    liftChain P (s ⋙ Functor.Elements.π P) (s.obj 0).val = s := by
  refine CategoryTheory.Functor.ext (fun i => Functor.Elements.ext _ _ rfl ?_) ?_
  · rw [eqToHom_refl, P.map_id]
    change P.map (s.map (homOfLE (Fin.zero_le i))).hom (s.obj 0).val = (s.obj i).val
    exact (s.map (homOfLE (Fin.zero_le i))).map_val
  · intro i j f
    apply Functor.Elements.Hom.ext
    have heq {x y : P.Elements} (h : x = y) :
        (eqToHom h).hom = eqToHom (congrArg (fun a : P.Elements => a.obj) h) := by
      subst h
      rfl
    simp [Functor.Elements.comp_hom, heq, liftChain]

private lemma singletonLabel {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex (coefficients P) n) :
    SSet.const (Y := (coefficients P).obj (s.1.obj 0))
      (show P.obj (s.1.obj 0) from SSet.yonedaEquiv s.2) = s.2 := by
  apply SSet.yonedaEquiv.injective
  rfl

instance : IsIso (elementsToReplacement P) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  rintro ⟨⟨n⟩⟩
  apply (isIso_iff_bijective _).2
  let dec (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex (coefficients P) n) :=
    liftChain P s.1 (SSet.yonedaEquiv s.2)
  have hl (s : ComposableArrows P.Elements n) :
      dec ((elementsToReplacement P).app (Opposite.op ⦋n⦌) s) = s :=
    liftChain_recover P s
  refine ⟨fun x y h => (hl x).symm.trans ((congrArg dec h).trans (hl y)), ?_⟩
  intro s
  refine ⟨dec s, Sigma.ext rfl ?_⟩
  apply heq_of_eq
  have e : P.map (s.1.map (homOfLE (Fin.zero_le (0 : Fin (n + 1))))) (SSet.yonedaEquiv s.2) =
      SSet.yonedaEquiv s.2 := by simp
  exact (congrArg (fun t => (SSet.const t : Δ[n] ⟶ (coefficients P).obj (s.1.obj 0))) e).trans
    (singletonLabel P s)

/-- 底の射列は厳密にそのまま保つ。 -/
lemma elementsToReplacement_projection :
    elementsToReplacement P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (coefficients P) =
      nerveMap (Functor.Elements.π P) := rfl

/-- 元の圏の nerve から選んだ小さい unstraightening への、底を保つ比較射。 -/
def elementsComparison : nerve P.Elements ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (spaceDiagram P) :=
  elementsToReplacement P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold (coefficients P) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallStraighteningReconstruction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (coefficients P)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveStraighteningUnitIso (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan)).symm

lemma elementsComparison_projection :
    elementsComparison P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (spaceDiagram P) =
      nerveMap (Functor.Elements.π P) := by
  simp only [elementsComparison, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso_projection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallStraighteningReconstruction_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_projection,
    elementsToReplacement_projection]

lemma elementsComparison_isPrecompositionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (elementsComparison P) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso (elementsToReplacement P))).comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isPrecompositionEquivalence (coefficients P)).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallStraighteningReconstruction_isPrecompositionEquivalence _).comp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence _)))

/- C3: compatibility declarations; use the specified Natural comparison. -/
attribute [deprecated
  "Use `SerrePositivity.InfinityCategories.SetWeight.\
  elementsComparisonNatural` from \
  `SerrePositivity.InfinityCategories.F2.Tensor.SetSectionsNaturality`."
  (since := "2026-11-05")]
  elementsComparison
attribute [deprecated
  "Use `SerrePositivity.InfinityCategories.SetWeight.\
  elementsComparisonNatural_projection` from \
  `SerrePositivity.InfinityCategories.F2.Tensor.SetSectionsNaturality`."
  (since := "2026-11-05")]
  elementsComparison_projection
attribute [deprecated
  "Use `SerrePositivity.InfinityCategories.SetWeight.\
  elementsComparisonNatural_isPrecompositionEquivalence` from \
  `SerrePositivity.InfinityCategories.F2.Tensor.SetSectionsNaturality`."
  (since := "2026-11-05")]
  elementsComparison_isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
