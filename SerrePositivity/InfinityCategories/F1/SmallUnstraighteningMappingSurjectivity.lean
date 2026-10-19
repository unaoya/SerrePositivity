module

public import SerrePositivity.InfinityCategories.F1.RelativeArrowSpecifiedRealization
public import SerrePositivity.InfinityCategories.F1.FunctorEdgeFromPrism
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingVertices
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningTransformationWitness
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningSmallness

/-!
概要：小さい底上の unstraightening の写像空間比較は頂点を同型まで被覆する。
方針：任意の底上の射を指定両端の collage で実現し持ち上げの選択空間で比較する。
規約：一般の非可逆な射を扱うが全写像空間の同値性はまだ主張しない。
使われ方：Kerodon Corollary 5.6.0.6 の写像空間比較の存在側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：任意の底上の射は写像空間比較の値と相対写像空間内で同型。
方針：指定した標準表現を両端に保って相対射を実現し選択した持ち上げと比較する。
規約：底が各次数で小さい場合。射の同値性は要求しない。
使われ方：写像空間比較の同値性へ進む頂点での全射性。 -/
lemma small_leftUnstraighteningMappingSpaceMap_surjective_up_to_iso
    {B : SSet.{u + 1}} [∀ n, Small.{u} (B.obj n)]
    (F G : B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F) :
    ∃ x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌,
      Nonempty (VertexIso ((leftUnstraighteningMappingSpaceMap F G).app _ x)
        (relativeFunctorVertex (leftUnstraighteningProjection G)
          (leftUnstraighteningProjection F) f hf)) := by
  obtain ⟨H, K, h₀, h₁, hk₀, hk₁, hkp⟩ :=
    exists_relativeArrow_specified_coherent_realization (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection G) f hf (unstraighteningTransportRepresentation F)
      (unstraighteningTransportRepresentation G)
  change prismEndpoint 0 B ≫ H = F at h₀
  change prismEndpoint 1 B ≫ H = G at h₁
  have hw₀ : prismEndpoint 0 _ ≫ K = pullback.fst pointedSpaceProjection F := by
    simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using hk₀
  have hw₁ : prismEndpoint 1 _ ≫ K = f ≫ pullback.fst pointedSpaceProjection G := by
    simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using hk₁
  let e := functorEdgeFromPrism H h₀ h₁
  have he : functorEdgePrism e = H := functorEdgeFromPrism_prism H h₀ h₁
  have hw : K ≫ pointedSpaceProjection =
      (Δ[1] ◁ leftUnstraighteningProjection F) ≫ functorEdgePrism e := by
    rw [he]
    exact hkp
  have h := leftUnstraighteningTransformationMapChoiceIso F G (functorEdgePrism e)
    (functorEdgePrism_zero e) (functorEdgePrism_one e)
    (leftUnstraighteningTransformationWitness F (functorEdgePrism e)
      (functorEdgePrism_zero e) K hw₀ hw)
  rw [leftUnstraighteningTransformationWitness_endpoint F G (functorEdgePrism e)
    (functorEdgePrism_zero e) (functorEdgePrism_one e) K hw₀ hw f hf hw₁] at h
  exact ⟨intervalMappingVertexOfEdge e,
    ⟨(leftUnstraighteningMappingSpaceMap_edgeVertexIso F G e).symm ≪≫ h⟩⟩

/-- 概要：小さい底上の unstraightening の写像空間比較は本質的全射。
方針：標的の任意の頂点を実際の相対射へ戻して実現定理を適用する。
規約：充満忠実性と写像空間全体の同値性は別途証明する。
使われ方：一般の coherent な変換の比較の存在側の公開界面。 -/
lemma small_leftUnstraighteningMappingSpaceMap_isEssentiallySurjective
    {B : SSet.{u + 1}} [∀ n, Small.{u} (B.obj n)]
    (F G : B ⟶ SpaceInfinity.{u}) :
    IsEssentiallySurjective (leftUnstraighteningMappingSpaceMap F G) := by
  intro y
  obtain ⟨⟨f, hf⟩, rfl⟩ :=
    (relativeFunctorVertexEquiv (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection F)).surjective y
  exact small_leftUnstraighteningMappingSpaceMap_surjective_up_to_iso F G f hf

end SerrePositivity.InfinityCategories
