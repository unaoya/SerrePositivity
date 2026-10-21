module

public import SerrePositivity.InfinityCategories.F1.CocartesianIntervalCompositionTriangle

/-!
概要：元の固定成分 Hom の正方形・三角形への制限は、全パラメーターの前合成と可換。
方針：元の prism の評価とテンソルの交換則で計算する。
規約：同じ第一三角形への写像の普遍族を保持する。
使われ方：第二三角形の外ホーン制限を同じ合成三角形写像と結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の関手圏 Hom の prism は、追加パラメーターの前合成と厳密に可換。 -/
lemma intervalFunctorHomPrism_precomp {A T B X : SSet.{u}} {F G : B ⟶ X}
    (i : A ⟶ T) (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) :
    ((Δ[1] ⊗ B) ◁ i) ≫ intervalFunctorHomPrism f = intervalFunctorHomPrism (i ≫ f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨t, b⟩, a⟩
  rfl

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (vertexFiber (cocartesianHomIntervalEvaluation F G c) v)

/-- 同じ固定成分 fiber の標準正方形は、全パラメーターの前合成と可換。 -/
lemma cocartesianIntervalHomSquare_precomp {A T : SSet.{u + 1}} (i : A ⟶ T) (f : T ⟶ E) :
    ((Δ[1] ⊗ Δ[1]) ◁ i) ≫ cocartesianIntervalHomSquare F G v f =
      cocartesianIntervalHomSquare F G v (i ≫ f) := by
  unfold cocartesianIntervalHomSquare cocartesianHomFixedComponentPrism
  rw [← Category.assoc, whisker_exchange, Category.assoc, intervalFunctorHomPrism_precomp,
    Category.assoc]

/-- 同じ二つの実際の三角形への制限は、全パラメーターの前合成と可換。 -/
lemma cocartesianIntervalHomTriangle_precomp {A T : SSet.{u + 1}}
    (j : Fin 2) (i : A ⟶ T) (f : T ⟶ E) :
    (Δ[2] ◁ i) ≫ cocartesianIntervalHomTriangle F G v j f =
      cocartesianIntervalHomTriangle F G v j (i ≫ f) := by
  unfold cocartesianIntervalHomTriangle
  rw [← Category.assoc, whisker_exchange, Category.assoc, cocartesianIntervalHomSquare_precomp]

/-- 同じ第一三角形の普遍制限写像は、任意の族でも元の第一三角形を展開で回収する。 -/
lemma cocartesianIntervalCompositionTriangleMap_uncurry {T : SSet.{u + 1}} (f : T ⟶ E) :
    innerTriangleExtensionUncurry (f ≫ cocartesianIntervalCompositionTriangleMap F G v) =
      cocartesianIntervalHomTriangle F G v 0 f := by
  unfold innerTriangleExtensionUncurry
  rw [Category.assoc, uncurry_natural_left]
  change (Δ[2] ◁ f) ≫ innerTriangleExtensionUncurry
    (cocartesianIntervalCompositionTriangleFamily F G v (𝟙 E)) = _
  rw [cocartesianIntervalCompositionTriangleFamily_uncurry,
    cocartesianIntervalHomTriangle_precomp, Category.comp_id]

end SerrePositivity.InfinityCategories
