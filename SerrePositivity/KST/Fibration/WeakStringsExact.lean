module
public import SerrePositivity.KST.Fibration.WeakStringsStability
public import SerrePositivity.KST.SConstruction.MultiRealization

/-! # W 列の単体的安定圏と反復 S 実現

全ての再添字の完全性を周囲の図式圏から反映する。
元の面・退化を保持し、K-1 の反復 S 関手を各段に適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の W 列の面・退化は完全である。 -/
lemma weakStringMap_preservesCofiberData {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    PreservesCofiberData (weakStringMap q θ) := by
  apply preservesCofiberData_fullSubcomplex_of_comp (weakStringPredicate q m)
  rw [weakStringMap_ι]
  exact (closedStableInclusion (weakStringClosedPredicate q n)).property.comp
    (diagramRestrictionMap B θ).property

/-- 同じ再添字を K-1 の完全関手として保持する。 -/
def weakStringExactMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) : weakStringModel q n ⟶ weakStringModel q m :=
  ⟨weakStringMap q θ, weakStringMap_preservesCofiberData q θ⟩

/-- 全 W 列を安定な入力と完全関手の単体的対象として束ねる。 -/
def weakStringStableSimplicial {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    SimplicialObject StableModel.{u} where
  obj n := weakStringModel q n.unop
  map θ := weakStringExactMap q θ.unop
  map_id n := Subtype.ext (weakStringMap_id q n.unop)
  map_comp θ φ := Subtype.ext (weakStringMap_comp q φ.unop θ.unop)

/-- 全ての W 列の各段へ反復 core S 実現を適用した単体的空間。 -/
def weakStringMultiRealization {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    SimplicialObject SSet.{u} :=
  weakStringStableSimplicial q ⋙ multiRealizationFunctor r

/-- W 列方向の面・退化は、元の完全な制限への反復 S 実現である。 -/
lemma weakStringMultiRealization_map {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (r : ℕ) {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n) :
    (weakStringMultiRealization q r).map θ =
      (multiRealizationFunctor r).map (weakStringExactMap q θ.unop) := rfl

end SerrePositivity.KST.Fibration
