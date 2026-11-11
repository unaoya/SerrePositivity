module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionNestedPureHom

/-!
概要：二重切断の中間対象から終対象への Hom を、可変な第二射の同じ座標で読む。
方針：既存の切断の最大座標の等式を使い、第二射を定値にはしない。
規約：全単体と全 native Hom の旗を保持する。
使われ方：二つの K 座標を分離した制御二胞体の内部合成条件。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 二重切断の第二 Hom は、可変な第二射を外側の最後の零座標で評価する。 -/
lemma controlledTriangleNestedSecondHom
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌)
    (s t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1))
    (hsi : s i = 0) (hi : t i = 1) (hj : s j = 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex σ τ s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_obj_middle σ τ s t i hsi hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionNestedCutSimplex_obj_last σ τ s t j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap s hsi j ≫ SSet.yonedaEquiv.symm τ := by
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut s j)) ≫ eqToHom _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_transport σ τ t
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero s i hsi) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one s j (by rw [hj]; decide))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_one X Y Z t i (by rw [hi]; decide))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Z n t),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_last σ τ t i (by rw [hi]; decide)]
  simp only [← Category.assoc]
  apply congrArg (fun f => f ≫ SSet.yonedaEquiv.symm τ)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_maximumMap s i j hsi (by rw [hj]; decide)).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap_front s hsi j).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
