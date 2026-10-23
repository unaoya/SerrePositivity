module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitNaturality

/-!
概要：単位の自然性の全正方形から、二三角形が共有する元の対角円柱を取り出す。
方針：二つの時間に同じ区間を入力し、両端と curry の式を照合する。
規約：対角辺を充填で選ばない。使われ方：元の二三角形の unstraightening 合成比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の単位正方形の同じ時刻の対角から得る、元の全円柱。 -/
def coherentColimitUnitDiagonal : SSet.Homotopy F
    (SSet.const (coherentDiagramTotalCocone G).vertex) where
  h := lift (𝟙 _) (snd _ (Δ[1] : SSet.{u + 1})) ≫ (coherentColimitUnitCylinder B H).h
  h₀ := by
    have he : SSet.ι₀ ≫ lift (𝟙 _) (snd ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1]) =
        SSet.ι₀ ≫ SSet.ι₀ := rfl
    rw [← Category.assoc, he, Category.assoc, (coherentColimitUnitCylinder B H).h₀]
    exact (coconeTransformationHomotopy (coherentDiagramTotalCocone F)).h₀
  h₁ := by
    have he : SSet.ι₁ ≫ lift (𝟙 _) (snd ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1]) =
        SSet.ι₁ ≫ SSet.ι₁ := rfl
    rw [← Category.assoc, he, Category.assoc, (coherentColimitUnitCylinder B H).h₁]
    exact (coconeTransformationHomotopy (coherentDiagramTotalCocone G)).h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 対角円柱は、元の全正方形の対角への制限を curry したものと厳密に一致。 -/
lemma coherentColimitUnitDiagonal_curry :
    curry (coherentColimitUnitDiagonal B H).h =
      squareDiagonal ≫ coherentColimitUnitSquare B H := by
  have hd : squareDiagonal.{u + 1} = lift (𝟙 Δ[1]) (𝟙 Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, coherentColimitUnitSquare, uncurry_curry]
  rw [hd]
  rfl

end SerrePositivity.InfinityCategories.F2
