module

public import SerrePositivity.InfinityCategories.F1.RelativeArrowCollageRepresentation
public import SerrePositivity.InfinityCategories.F1.TransportRepresentationCartesianRestriction

/-!
概要：小さい left fibration 間の任意の相対射を coherent な区間図式に実現する。
方針：collage を分類し両端の cartesian 正方形で表現を戻す。
規約：両端の表現は構成から得られ、指定済みの表現とはまだ同一視しない。
使われ方：非可逆な写像空間比較の存在側の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：任意の小さい相対射は両端の表現と整合する coherent な区間図式を持つ。
方針：collage の分類図式と元の始域からの標準 prism を使う。
規約：元の射 f は可逆性・単射性の仮定なしで右端に厳密に現れる。
使われ方：指定した両端表現への相対化の前の一般射の実現。 -/
lemma exists_relativeArrow_coherent_realization {E F B : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (F.obj n)]
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    ∃ (R₀ : LeftTransportRepresentation p) (R₁ : LeftTransportRepresentation q)
      (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
      (K : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u}),
      prismEndpoint 0 B ≫ H = R₀.diagram ∧
      prismEndpoint 1 B ≫ H = R₁.diagram ∧
      prismEndpoint 0 E ≫ K = R₀.pointedMap ∧
      prismEndpoint 1 E ≫ K = f ≫ R₁.pointedMap ∧
      K ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ H := by
  have := relativeArrowCollageProjection_leftFibration p q f hf
  obtain ⟨R⟩ := relativeArrowCollageRepresentation_nonempty p q f hf
  let h₀ := relativeArrowCollage_inl_isPullback p q f hf
  let h₁ := relativeArrowCollage_inr_isPullback f q
  let R₀ := R.cartesianRestrict (relativeJoinInl f (𝟙 F)) (prismEndpoint 0 B) h₀
  let R₁ := R.cartesianRestrict (relativeJoinInr f (𝟙 F)) (prismEndpoint 1 B) h₁
  refine ⟨R₀, R₁, R.diagram, relativeJoinPrism f ≫ R.pointedMap, rfl, rfl, ?_, ?_, ?_⟩
  · rw [← Category.assoc, relativeJoinPrism_zero]
    exact (R.cartesianRestrict_pointedMap _ _ h₀).symm
  · rw [← Category.assoc, relativeJoinPrism_one, Category.assoc]
    exact congrArg (fun k ↦ f ≫ k) (R.cartesianRestrict_pointedMap _ _ h₁).symm
  · rw [Category.assoc, R.pointedMap_projection, ← Category.assoc,
      relativeArrowCollageProjection_prism p q f hf]

end SerrePositivity.InfinityCategories
