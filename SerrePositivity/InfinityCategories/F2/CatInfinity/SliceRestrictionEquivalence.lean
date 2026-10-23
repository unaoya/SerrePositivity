module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.SliceRestrictionEquivalenceLifting

/-!
概要：同値な形状による slice の制限は trivial Kan fibration。
方針：部分複体の境界充填を証明し、任意の単射を像を経由して処理する。
規約：形状とその部分図式は任意の単体集合。
使われ方：Cat_∞ の極限錐を可逆円柱に沿って輸送する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：同値な部分図式への slice 制限は trivial Kan fibration。
方針：全ての境界包含に対する持ち上げ性を適用する。
規約：値域は quasicategory、形状の quasicategory 性は不要。
使われ方：可逆円柱の端点への錐の制限。 -/
lemma sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence_subcomplex
    {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) (K₀ : K.Subcomplex)
    (hK : IsPrecompositionEquivalence K₀.ι) : TrivialKanFibration (sliceOverRestrict p K₀.ι) :=
  (trivialKanFibration_iff_boundary _).2
    (fun n => sliceOverRestrict_lift_of_precompositionEquivalence p (boundary n) K₀ hK)

/-- 概要：同値条件を持つ任意の単射への slice 制限は trivial Kan fibration。
方針：像への同型と部分複体の包含に分解する。
規約：射の表示は任意。
使われ方：可逆円柱の両端からの錐の輸送。 -/
lemma sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence
    {K L X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) (f : L ⟶ K) [Mono f]
    (hf : IsPrecompositionEquivalence f) : TrivialKanFibration (sliceOverRestrict p f) := by
  let R : K.Subcomplex := Subfunctor.range f
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono f
  have hR : IsPrecompositionEquivalence R.ι :=
    (isPrecompositionEquivalence_of_iso (asIso (Subfunctor.toRange f))).cancel_left hf
  have hT := sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence_subcomplex p R hR
  have := sliceOverRestrict_isIso (R.ι ≫ p) (Subfunctor.toRange f)
  have he : f = Subfunctor.toRange f ≫ R.ι := rfl
  rw [he, sliceOverRestrict_comp]
  constructor
  exact trivialKanFibrations.comp_mem _ _ hT.mem (MorphismProperty.rlp_of_isIso _ _)

end SerrePositivity.InfinityCategories.F2
