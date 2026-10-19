module

public import SerrePositivity.InfinityCategories.F1.RelativeArrowFamilyRealization
public import SerrePositivity.InfinityCategories.F1.FunctorPrismFamilyCurry
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningSmallness
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorSmallness

/-!
概要：相対射の小さい族を変換空間への実際の射と pointed な prism へ復元する。
方針：積の底上の指定両端 collage を分類し図式の族を二度 curry する。
規約：選択はパラメーター空間全体について一度だけ行う。
使われ方：写像空間比較の逆向きの射とその全体での整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：区間付きの底変換は結合子と可換。
方針：各次数の三つの成分で計算する。
規約：パラメーター K は最後の因子。
使われ方：復元した prism の射影の式を既存の族の表示へ移す。 -/
lemma parameterizedPrism_associator_naturality {E B : SSet.{u}}
    (p : E ⟶ B) (K : SSet.{u}) :
    (α_ (Δ[1] : SSet.{u}) E K).hom ≫ (Δ[1] ◁ (p ▷ K)) =
      ((Δ[1] ◁ p) ▷ K) ≫ (α_ Δ[1] B K).hom := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 概要：小さい相対射の族を coherent な変換空間への射として復元する。
方針：指定した標準表現を両端に保つ collage を分類し curry する。
規約：全パラメーターの始点・終点・底の条件を同時に保持する。
使われ方：比較射の右逆を作る普遍的な族への適用。 -/
lemma exists_small_coherentFamily_recovery {B K : SSet.{u + 1}}
    [∀ n, Small.{u} (B.obj n)] [∀ n, Small.{u} (K.obj n)]
    (F G : B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G =
      fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F) :
    ∃ (t : K ⟶ leftUnstraighteningTransformationSpace F G)
      (W : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗ K ⟶
        PointedSpaceInfinity.{u}),
      (prismEndpoint 0 (leftUnstraightening F) ▷ K) ≫ W =
        fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F ∧
      (prismEndpoint 1 (leftUnstraightening F) ▷ K) ≫ W =
        f ≫ pullback.fst pointedSpaceProjection G ∧
      W ≫ pointedSpaceProjection = ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K) ≫
        functorParameterizedPrism (intervalMappingUncurry t) := by
  obtain ⟨H, W, h₀, h₁, hw₀, hw₁, hwp⟩ :=
    exists_relativeArrowFamily_specified_coherent_realization (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection G) f hf (unstraighteningTransportRepresentation F)
      (unstraighteningTransportRepresentation G)
  change prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ F at h₀
  change prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ G at h₁
  let t := coherentTransformationFamilyCurry F G H h₀ h₁
  refine ⟨t, (α_ Δ[1] (leftUnstraightening F) K).hom ≫ W, ?_, ?_, ?_⟩
  · rw [← Category.assoc, prismEndpoint_associator]
    simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using hw₀
  · rw [← Category.assoc, prismEndpoint_associator]
    simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using hw₁
  · rw [Category.assoc, hwp, ← Category.assoc, parameterizedPrism_associator_naturality,
      Category.assoc, coherentTransformationFamilyCurry_prism]

end SerrePositivity.InfinityCategories
