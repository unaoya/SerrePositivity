module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RightConeCoefficient
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.JoinTensorLeftMiddle

/-!
概要：実錐への全係数の追加は、元の左因子の全写像に厳密に自然。
方針：直積と join の比較の自然性と、元の二係数の交換を貼る。
規約：実全図式を保持。使われ方：標準単体錐の添字制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の左錐因子の写像と全係数の追加は、実全図式で可換。 -/
lemma rightConeCoefficient_naturality {A B : SSet.{u}} (f : A ⟶ B) (P : SSet.{u}) :
    (P ◁ joinMap f (𝟙 Δ[0])) ≫ rightConeCoefficient B P =
      rightConeCoefficient A P ≫ joinMap (f ▷ P) (𝟙 Δ[0]) := by
  have hb : (P ◁ f) ≫ (β_ P B).hom = (β_ P A).hom ≫ (f ▷ P) := by
    apply SSet.hom_ext
    intro n
    rfl
  have hh : joinMap (P ◁ f) (𝟙 (Δ[0] : SSet.{u})) ≫
      joinMap (β_ P B).hom (𝟙 Δ[0]) =
    joinMap (β_ P A).hom (𝟙 Δ[0]) ≫ joinMap (f ▷ P) (𝟙 Δ[0]) := by
    simp only [← joinMap_comp, Category.id_comp, hb]
  unfold rightConeCoefficient
  rw [← Category.assoc, joinTensorLeft_middle_naturality, Category.assoc, hh,
    ← Category.assoc]

end SerrePositivity.InfinityCategories.F2
