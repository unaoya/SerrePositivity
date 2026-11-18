module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.RightKanTransportUniverse
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightTransportPostcomp
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableLimitCharacterization

/-!
概要：指定右 Kan 輸送の宇宙移送と後合成を、元の局所全錐の像へ比較する。
方針：同じ実形状の同型に沿った再添字付けと、全錐の全射の等式を使う。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の全表現可能関手による降下の検出。
規約：任意の係数への後合成に極限保存性を仮定しない。必要な局所極限性を明示する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 後合成した宇宙移送の極限性は、元の全局所錐の宇宙移送の同じ像で判定できる。 -/
lemma kanRightTransportUliftPostcomp_isLimit_iff {K C D : SSet.{u}}
    {E : SSet.{max u v}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) (U : (SSet.uliftFunctor.{v, u}).obj D ⟶ E) :
    IsLimitCone (mapJoinCone U (JoinCone.ulift.{u, v} t.cone)) ↔
      IsLimitCone (kanRightTransportPostcomp (kanRightTransportUlift.{u, v} t) U).cone := by
  let e := (rightKanShapeUniverseIso.{u, v} δ c).symm
  let d := (mapJoinCone U (JoinCone.ulift.{u, v} t.cone)).reindexIso e
  apply (isLimitCone_iff_reindexIso (mapJoinCone U (JoinCone.ulift.{u, v} t.cone)) e).trans
  apply isLimitCone_iff_of_diagram_eq (c := d)
    (d := (kanRightTransportPostcomp (kanRightTransportUlift.{u, v} t) U).cone)
  · change (rightKanShapeUniverseIso.{u, v} δ c).inv ≫
      ((SSet.uliftFunctor.{v, u}).map (rightKanDiagram δ F₀ c) ≫ U) =
      rightKanDiagram ((SSet.uliftFunctor.{v, u}).map δ)
        ((SSet.uliftFunctor.{v, u}).map F₀ ≫ U) (ULift.up c)
    dsimp only [rightKanDiagram]
    rw [Functor.map_comp, ← Category.assoc, ← Category.assoc,
      rightKanShapeUniverseIso_inv_projection, Category.assoc]
  · rw [kanRightTransportPostcomp_cone_val, kanRightTransportUlift_cone_val]
    change joinMap (𝟙 (Δ[0] : SSet.{max u v})) (rightKanShapeUniverseIso.{u, v} δ c).inv ≫
      (((uliftConeShapeIso.{u, v} (rightKanShape δ c) 0).inv ≫
        (SSet.uliftFunctor.{v, u}).map t.cone.val) ≫ U) = _
    simp only [rightKanConeUniverseIso, Iso.trans_inv, joinIso, Iso.refl_inv, Category.assoc]

/-- 元の指定局所錐の同じ像の極限性から、移送した指定余単位の右 Kan 条件を得る。 -/
lemma kanRightKanExtension_ulift_postcomp_of_localLimits {K C D : SSet.{u}}
    {E : SSet.{max u v}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} (hα : IsRightKanExtension δ F₀ F α)
    (U : (SSet.uliftFunctor.{v, u}).obj D ⟶ E)
    (hU : ∀ (c : C _⦋0⦌) (t : RightKanConeTransport δ F₀ F α c), IsLimitCone t.cone →
      IsLimitCone (mapJoinCone U (JoinCone.ulift.{u, v} t.cone))) :
    IsRightKanExtension ((SSet.uliftFunctor.{v, u}).map δ)
      ((SSet.uliftFunctor.{v, u}).map F₀ ≫ U) ((SSet.uliftFunctor.{v, u}).map F ≫ U)
      (kanRightCounitPostcomp (kanRightCounitUlift.{u, v} α) U) := by
  rintro ⟨c⟩
  obtain ⟨t, ht⟩ := hα c
  exact ⟨kanRightTransportPostcomp (kanRightTransportUlift.{u, v} t) U,
    (kanRightTransportUliftPostcomp_isLimit_iff t U).mp (hU c t ht)⟩

/-- 元の指定右 Kan 延長を全共変表現可能関手へ写しても、同じ指定余単位の右 Kan 条件を持つ。 -/
lemma kanRightKanExtension_covariantRepresentable {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀}
    (hα : IsRightKanExtension δ F₀ F α) (x : D _⦋0⦌) :
    IsRightKanExtension ((SSet.uliftFunctor.{u + 1, u}).map δ)
      ((SSet.uliftFunctor.{u + 1, u}).map F₀ ≫ covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ covariantRepresentableInfinity x)
      (kanRightCounitPostcomp (kanRightCounitUlift.{u, u + 1} α)
        (covariantRepresentableInfinity x)) := by
  apply kanRightKanExtension_ulift_postcomp_of_localLimits hα (covariantRepresentableInfinity x)
  intro c t ht
  exact covariantRepresentableInfinity_isLimit t.cone ht x

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
