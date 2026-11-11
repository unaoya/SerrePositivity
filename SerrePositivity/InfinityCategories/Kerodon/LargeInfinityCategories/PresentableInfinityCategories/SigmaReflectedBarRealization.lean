module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaReflectedBarDegree
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafBarRealization

/-!
概要：全前層の元の bar に専用反映を適用した simplicial Ind 実現。
方針：同じ幾何学的実現を左随伴で保存し、可逆余単位で元の P_Σ 対象へ戻す。
規約：元の bar・反映・全余錐を保持する。
使われ方：P_Σ の filtered 余極限と幾何学的実現による生成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：元の前層 bar の反映は、各項が Ind に属し、元の P_Σ 対象を実現する。
方針：元の実現の保存と反映の同じ可逆余単位を合成する。
規約：別の単体的図式へ置き換えず、構成済みの bar と L の合成を使う。
使われ方：採用した専用反映経路による simplicial Ind 表示。 -/
lemma sigmaReflector_bar_realization {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    {L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C}
    (β : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ L))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) L β)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarObject (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor v) ≫ L),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso d.vertex v) ∧
      ∀ n : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u}, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex Cardinal.aleph0 C
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarObject (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor v) ≫ L).app
            (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)))) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor v
  obtain ⟨c, hc, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafBarObject_realization F
  have hLc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.mapJoinCocone_isColimit_of_adjunction_of_quasicategoryShape
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaReflectorAdjunction β hβ) c hc
  obtain ⟨ε, hε⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaReflector_exists_counit β hβ
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaReflector_counit_isIso β hβ ε hε
  let eε : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C ≫ L) (𝟙 _) := asIso ε
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) v :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor_vertex v
  let ev : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone L c).vertex v :=
    eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex L c)) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e L ≪≫
      eqToIso (congrArg HomotopyCategory.mk (congrArg (L.app (Opposite.op ⦋0⦌)) hv)) ≪≫
      eε.app v
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone L c, hLc, ⟨ev⟩, fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaReflector_barDegree_isInd hC β hβ F n⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
