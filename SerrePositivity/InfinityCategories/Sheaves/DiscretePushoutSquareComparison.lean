module

public import SerrePositivity.InfinityCategories.Sheaves.DiscretePushoutSquareData
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictNativeCoconeTriangles
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.StrictSpanHornEdges
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitReindex

/-!
概要：元の離散押し出し四角形を、同じ通常の押し出し余錐の実現へ同定する。
方針：span の二辺と指定合成二単体を比較し、二三角形の押し出しの外延性を用いる。
  文献対応：HTT 4.2.4.1・6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）、S8-3。
規約：型は drafts の IsPushoutSquare と任意の余極限頂点の離散性の積のまま。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q R : Cᵒᵖ ⥤ Type u}

private lemma pushoutTriangleShape_left :
    spanCoconeTriangleLeft ≫ joinMap (strictSpanHornIso.{u, u + 1}).inv (𝟙 Δ[0]) =
      strictCoconeLegTriangleShape.{u, u + 1} (AsSmall.up.map WalkingSpan.Hom.fst) := by
  rw [spanCoconeTriangleLeft, Category.assoc, ← joinMap_comp, Category.id_comp,
    strictSpanHornIso_inv_left_edge]
  rfl

private lemma pushoutTriangleShape_right :
    spanCoconeTriangleRight ≫ joinMap (strictSpanHornIso.{u, u + 1}).inv (𝟙 Δ[0]) =
      strictCoconeLegTriangleShape.{u, u + 1} (AsSmall.up.map WalkingSpan.Hom.snd) := by
  rw [spanCoconeTriangleRight, Category.assoc, ← joinMap_comp, Category.id_comp,
    strictSpanHornIso_inv_right_edge]
  rfl

/-- 元の押し出し余錐の全射は、ホーン表示へ制限すると元の四角形の全余錐と一致。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）。二つの指定合成二単体を保つ。 -/
lemma discretePushoutCocone_square_val (f : P ⟶ Q) (g : P ⟶ R) :
    ((discretePushoutCocone f g).restrict (strictSpanHornIso.{u, u + 1}).inv).val =
      (pushoutCocone (discretePushoutSquare f g)).val := by
  apply spanCocone_isPushout.hom_ext
  · change spanCoconeTriangleLeft ≫
        (joinMap (strictSpanHornIso.{u, u + 1}).inv (𝟙 Δ[0]) ≫
          (discretePushoutCocone f g).val) =
      spanCoconeTriangleLeft ≫ (spanCoconeSquareIso.hom ≫ discretePushoutSquare f g)
    rw [← Category.assoc, pushoutTriangleShape_left,
      ← Category.assoc spanCoconeTriangleLeft spanCoconeSquareIso.hom,
      spanCoconeSquareIso_left, discretePushoutSquare_triangle_left]
    change strictCoconeLegTriangleShape (AsSmall.up.map WalkingSpan.Hom.fst) ≫
      ((strictNativeCocone ((kanDiscretePresheafFunctor C).mapCocone
        ((pushout.cocone f g).whisker (AsSmall.down : AsSmall.{u} WalkingSpan ⥤ _)))).val ≫
        kanDiagramRealization Cᵒᵖ) = _
    rw [← Category.assoc, strictNativeCocone_triangle_val]
    rfl
  · change spanCoconeTriangleRight ≫
        (joinMap (strictSpanHornIso.{u, u + 1}).inv (𝟙 Δ[0]) ≫
          (discretePushoutCocone f g).val) =
      spanCoconeTriangleRight ≫ (spanCoconeSquareIso.hom ≫ discretePushoutSquare f g)
    rw [← Category.assoc, pushoutTriangleShape_right,
      ← Category.assoc spanCoconeTriangleRight spanCoconeSquareIso.hom,
      spanCoconeSquareIso_right, discretePushoutSquare_triangle_right]
    change strictCoconeLegTriangleShape (AsSmall.up.map WalkingSpan.Hom.snd) ≫
      ((strictNativeCocone ((kanDiscretePresheafFunctor C).mapCocone
        ((pushout.cocone f g).whisker (AsSmall.down : AsSmall.{u} WalkingSpan ⥤ _)))).val ≫
        kanDiagramRealization Cᵒᵖ) = _
    rw [← Category.assoc, strictNativeCocone_triangle_val]
    rfl

/-- 単射を一脚とする元の離散四角形は、その指定余錐そのものが余極限。
HTT 6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）、型を変えない S8-3 の第一成分。 -/
lemma discretePushoutSquare_isPushout (f : P ⟶ Q) (g : P ⟶ R) [Mono f] :
    IsPushoutSquare (discretePushoutSquare f g) := by
  have h := (isColimitCone_iff_restrict_of_isIso (discretePushoutCocone f g)
    (strictSpanHornIso.{u, u + 1}).inv).mp (discretePushoutCocone_isColimit f g)
  exact (isColimitCone_iff_of_cocone_val_eq _ _
    (discretePushoutCocone_square_val f g)).mp h

private lemma discretePushoutCocone_restrict_vertex (f : P ⟶ Q) (g : P ⟶ R) :
    ((discretePushoutCocone f g).restrict (strictSpanHornIso.{u, u + 1}).inv).vertex =
      (discretePushoutCocone f g).vertex := by
  rw [JoinCocone.vertex_eq, JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (joinInr _ Δ[0] ≫
    (joinMap (strictSpanHornIso.{u, u + 1}).inv (𝟙 Δ[0]) ≫
      (discretePushoutCocone f g).val)) = _
  rw [← Category.assoc, joinInr_joinMap, Category.id_comp]

/-- 元の離散押し出し四角形の任意の余極限頂点も離散。
HTT 6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）。drafts と同じ両成分を結論する。 -/
lemma discretePushout_isDiscrete (f : P ⟶ Q) (g : P ⟶ R) [Mono f] :
    IsPushoutSquare (discretePushoutSquare f g) ∧
      ∀ c : JoinCocone (pushoutSpan (discretePushoutSquare f g)),
        IsColimitCone c → Is0Truncated c.vertex := by
  have hp := discretePushoutSquare_isPushout f g
  refine ⟨hp, ?_⟩
  intro c hc
  have hv : ((discretePushoutCocone f g).restrict
      (strictSpanHornIso.{u, u + 1}).inv).vertex =
      (pushoutCocone (discretePushoutSquare f g)).vertex := by
    rw [JoinCocone.vertex_eq, JoinCocone.vertex_eq, discretePushoutCocone_square_val]
    rfl
  have hz : Is0Truncated (pushoutCocone (discretePushoutSquare f g)).vertex := by
    rw [← hv, discretePushoutCocone_restrict_vertex]
    change Is0Truncated (discretePresheafCocone _).vertex
    rw [discretePresheafCocone_vertex]
    exact is0Truncated_discretePresheaf _
  exact hz.of_vertexIso (colimitVertexIso c _ hc hp)

end SerrePositivity.InfinityCategories.Sheaves
