module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanEndFibration
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanParameterizedRealization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor

/-!
概要：BKパラメータ付き実現はanodyne射を自明cofibrationへ送る。
方針：frame Homのfibration性とBK endの保存性を、同じ実現随伴で移す。
使われ方：HTT 4.2.4.4、RR02(a)の実際のframeのhorn条件。
規約：SSetモデル構造を使わず、Cのモデル構造の持ち上げ判定を使う。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

include hA hconst in
/-- 固定した右随伴は、CのfibrationをKan fibrationへ送る。 -/
lemma bousfieldKanParameterHom_fibration {Y Z : C} (p : Y ⟶ Z) [Fibration p] :
    Fibration ((hom K A ⋙ weightedSectionsFunctor (bousfieldKanWeight Kᵒᵖ)).map p) := by
  have : ∀ k, Fibration (((hom K A).map p).app k) := by
    intro k
    exact HomotopyFunctionComplex.cosimplicialHom_fibration
      (A.obj k.unop) (hA k.unop) (hconst k.unop) p
  exact bousfieldKanEndMap_fibration Kᵒᵖ ((hom K A).map p)

include hA hconst in
/-- 同じ実現随伴による、anodyne射の自明cofibrationへの移送。 -/
lemma bousfieldKanParameterRealization_map_anodyne {U V : SSet.{w}}
    (i : U ⟶ V) (hi : SSet.anodyneExtensions i) :
    trivialCofibrations C ((bousfieldKanParameterRealization K A).map i) := by
  rw [← fibrations_llp C]
  intro Y Z p hp
  have : Fibration p := ⟨hp⟩
  have := bousfieldKanParameterHom_fibration K A hA hconst p
  apply ((bousfieldKanParameterAdjunction K A).hasLiftingProperty_iff i p).mpr
  exact hi _ ((fibration_iff _).mp inferInstance)

end SerrePositivity.DiagramModel.FrameWeightRealization
