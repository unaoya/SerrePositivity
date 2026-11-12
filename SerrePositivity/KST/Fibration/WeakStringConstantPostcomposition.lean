module
public import SerrePositivity.KST.Fibration.WeakStringConstantNaturality
public import SerrePositivity.KST.Fibration.WeakStringPostNaturality
public import SerrePositivity.KST.Fibration.WeakStringRealizationConstants

/-! # 元の定数 W 列と包含側の完全関手の厳密な可換四角形 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の K-5 完全関手を、同じ射のまま K-1/K-2 の安定な入力の射として保持する。 -/
def sInputExactMap {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    sInputModel A ⟶ sInputModel B :=
  ⟨f.hom, (exactMap_preservesSData f).toCofiberData⟩

/-- 元の定数 W 列は、元の包含側の完全関手による後合成を厳密に保つ。 -/
lemma weakStringConstantExact_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : SimplexCategory) :
    weakStringConstantExact (f ≫ q : A ⟶ C) n ≫ weakStringPostExact f q n =
      sInputExactMap f ≫ weakStringConstantExact q n := by
  apply Subtype.ext
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι).1
  change ((weakStringConstantExact (f ≫ q : A ⟶ C) n).val ≫ weakStringPostMap f q n) ≫ _ =
    (f.hom ≫ (weakStringConstantExact q n).val) ≫ _
  simp only [Category.assoc, weakStringPostMap_ι, weakStringConstantExact_ι]
  rw [← Category.assoc, weakStringConstantExact_ι]
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_curry, uncurry_natural_left, uncurry_curry,
    whiskerLeft_snd]
  rfl

/-- 元の定数包含の実対角の写像は、任意の実現関手の下で同じ完全関手の四角形を保つ。 -/
theorem weakStringRealizationConstantDiagonal_postcomp
    (F : StableModel.{u} ⥤ SSet.{u}) {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    F.map (sInputExactMap f) ≫ weakStringRealizationConstantDiagonal F q =
      weakStringRealizationConstantDiagonal F (f ≫ q : A ⟶ C) ≫
        simplicialDiagonalFunctor.map
          (Functor.whiskerRight (weakStringStablePostcomp f q) F) := by
  apply NatTrans.ext
  funext n
  change (F.map (sInputExactMap f)).app n ≫
      (F.map (weakStringConstantExact q n.unop)).app n =
    (F.map (weakStringConstantExact (f ≫ q : A ⟶ C) n.unop)).app n ≫
      (F.map (weakStringPostExact f q n.unop)).app n
  rw [← NatTrans.comp_app, ← F.map_comp, ← NatTrans.comp_app, ← F.map_comp,
    weakStringConstantExact_postcomp]

end SerrePositivity.KST.Fibration
