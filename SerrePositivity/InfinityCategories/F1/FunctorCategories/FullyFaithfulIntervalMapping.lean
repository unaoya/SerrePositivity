module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostHomCriterion
public import SerrePositivity.InfinityCategories.F1.Transport.ParametrizedPointTransportSquare

/-!
概要：充満忠実な元の射は、区間模型の実際の Hom 作用にも同値を誘導する。
方針：標準 pinched Hom との自然性を使い、両側の模型比較の同値を消去する。
規約：元の射の intervalMappingPost そのものについて述べる。
使われ方：局所化による図式制限の充満忠実性を、c1 の全変換空間の制限へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 充満忠実な射の実際の区間 Hom への作用は、全対象対で同値。 -/
lemma IsFullyFaithful.intervalMappingPost_isQCatEquivalence
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : IsFullyFaithful f) (x y : X _⦋0⦌) :
    IsQCatEquivalence (intervalMappingPost f x y) := by
  have h := (hf x y).isQCatEquivalence.comp
    (pinchedHomToIntervalMappingSpace_isQCatEquivalence (f.app _ x) (f.app _ y))
  have hc := pinchedHomToIntervalMappingSpace_postOfEq f x y rfl rfl
  simp only [eqToHom_refl, Category.comp_id, intervalMappingPostOfEq_refl] at hc
  rw [hc] at h
  exact (pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).cancel_left h

end SerrePositivity.InfinityCategories
