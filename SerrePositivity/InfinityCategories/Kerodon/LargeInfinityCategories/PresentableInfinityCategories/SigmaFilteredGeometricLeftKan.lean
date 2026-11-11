module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomWeightColimitConstruction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaSimplicialIndDiagram
public import SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.SigmaGeometricRealizations
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaLeftKanExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndLeftKanExtension

/-!
概要：filtered 余極限と幾何学的実現から P_Σ の局所左 Kan 余極限を作る。
方針：Ind 延長の単体的実現を全 Hom 係数族を通して密度表示へ移す。
規約：標的の全 sifted 余極限を存在仮定にしない。
使われ方：P_Σ 普遍性の弱い標的条件での延長存在。

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


/-- 概要：任意の P_Σ 対象は前層圏でも単体的 Ind 表示を持つ。
方針：包含が保つ幾何学的実現を元の Ind 値図式へ移す。
規約：頂点は元の前層密度余錐と比較する。
使われ方：弱い標的条件での局所余極限構成。 -/
lemma sigma_exists_ambientIndRealization
    {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    ∃ (R : (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u}) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity Cardinal.aleph0 C)
      (cP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf Cardinal.aleph0 C)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cP ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso cP.vertex
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor v)).vertex) := by
  obtain ⟨R, H, d, heq, hd, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheaf_simplicialIndDiagram C hC v
  refine ⟨R, ?_⟩
  rw [heq]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) d,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.sigmaInclusion_geometricRealization_isColimit H d hd, ⟨?_⟩⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C)

/-- 概要：filtered 余極限と幾何学的実現だけで各 P_Σ 密度図式の像を実現できる。
方針：Ind 延長を作り、単体的 Ind 表示の像を実現して Hom 表現可能性へ戻す。
規約：元の小さい元の圏と元の標的を保持する。
使われ方：元の P_Σ Yoneda に沿う局所左 Kan 余極限。 -/
lemma sigmaElements_hasColimit_of_filtered_geometric
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits Cardinal.aleph0 D)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallGeometricRealizations D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor v)) ≫ F₀) := by
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  obtain ⟨G, β, hβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_leftKanExtension Cardinal.aleph0 hD F₀
  obtain ⟨R, cP, hcP, ⟨eP⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigma_exists_ambientIndRealization hC v
  obtain ⟨cD, hcD⟩ := hG (R ≫ G)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasColimit_of_indPresentation_realization Cardinal.aleph0 β hβ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor v))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit _) R cP hcP eP cD hcD

/-- 概要：弱い標的条件でも元の P_Σ 局所左 Kan 図式に余極限がある。
方針：元の元の圏と元の comma 添字の同値に沿って余極限を移す。
規約：指定した元の図式を結論に保持する。
使われ方：全局所左 Kan 存在定理への入力。 -/
lemma sigmaLeftKanDiagram_hasColimit_of_filtered_geometric
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits Cardinal.aleph0 D)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallGeometricRealizations D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) F₀ v) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasColimit_of_equivalentRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaElementsLeftKanComparison v)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaElementsLeftKanComparison_isQCatEquivalence v)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaElementsLeftKanComparison_diagram]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaElements_hasColimit_of_filtered_geometric hC hD hG F₀ v

/-- 概要：filtered 余極限と幾何学的実現を持つ標的へ元の左 Kan 延長が存在する。
方針：構成した全局所余極限を全左 Kan 存在定理に渡す。
規約：元の Yoneda と指定単位を保持する。
使われ方：弱い標的条件での Yoneda 制限の本質的全射性。 -/
lemma sigma_exists_leftKanExtension_of_filtered_geometric
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits Cardinal.aleph0 D)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallGeometricRealizations D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    ∃ (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C ⟶ D)
      (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ G)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) F₀ G β :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_of_local_colimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) F₀
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanDiagram_hasColimit_of_filtered_geometric hC hD hG F₀)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
