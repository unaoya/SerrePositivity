module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationSuffixCorrection
/-!
概要：同じ実二次切断和を、候補の左補正の後合成と右補正の前合成へ移す。
方針：実三重合成の相付き還元と、左右それぞれの実補正との総和相殺を結合する。
規約：二次切断和全体を計算し、仮定として要求しない。
使われ方：実候補の微分を候補の全二次境界へ接続する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ全実二次切断和は、候補の左右補正の同じ合成和と相殺する。 -/
lemma dgModuleAugmentationCutQuadraticBoundary_corrections_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutQuadraticBoundary R C E F s I a b k j) +
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationImageCorrection R C E F s β I a b k l) +
    (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSuffixCorrection R C E F s β I a b k j) = 0 := by
  let U := ∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
    ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedImageRight R C E F s I a b k j l)
  let V := ∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
    ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
    ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
      (if β l = 1 ∧ ¬ β j = 1 then
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0))
  let L := ∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationImageCorrection R C E F s β I a b k l
  let T := ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSuffixCorrection R C E F s β I a b k j
  have hq :
      (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutQuadraticBoundary R C E F s I a b k j) = U + V :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutQuadraticBoundary_sum_reduction R C E F s β I a b k hk
  have hl : U + L = 0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationImageCorrection_sum_cancel R C E F s β I a b k hk
  have hr : T + V = 0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSuffixCorrection_sum_cancel R C E F s β I a b k hk
  change _ + L + T = 0
  rw [hq]
  calc
    U + V + L + T = (U + L) + (T + V) := by abel
    _ = 0 := by rw [hl, hr, add_zero]
/-- 実混合候補の微分を、同じ候補の左右補正の合成と比較差で表す。 -/
lemma dgModuleAugmentationPrismMixedHom_differential_corrections
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    let base := _root_.SerrePositivity.DifferentialGraded.compose R
      (x := (s.obj a).replacement.val) (y := (s.obj b).replacement.val)
      (z := F.obj (s.obj b).source) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationComponent R C E F (s.obj b)).val
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) (add_zero k)
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData β I a b k hI ha hb hk) =
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1) base +
    (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection R C E F s.toSimplexData β (I.erase j) a b (k + 1)) -
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationImageCorrection R C E F s.toSimplexData β I a b k l) -
    (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSuffixCorrection R C E F s.toSimplexData β I a b k j) -
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l) := by
  dsimp only
  have hc :
      (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k j) =
      -((∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationImageCorrection R C E F s.toSimplexData β I a b k l) +
        (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSuffixCorrection R C E F s.toSimplexData β I a b k j)) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc] using
      dgModuleAugmentationCutQuadraticBoundary_corrections_cancel R C E F s.toSimplexData
        β I a b k hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom_differential_reduction R C E F s β I a b k
    hI ha hb hk, hc]
  abel
end SerrePositivity.InfinityCategories.Project.DerivedCategories
