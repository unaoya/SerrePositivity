module

public import SerrePositivity.InfinityCategories.F1.RelativeArrowFamilyRealization
public import SerrePositivity.InfinityCategories.F1.TransportRepresentationFamilyRecovery
public import SerrePositivity.InfinityCategories.F1.FunctorPrismFamilyCurry
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningSmallness
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorSmallness

/-!
概要：相対射の族を変換空間への実際の射と pointed な prism へ復元する。
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

/-- 概要：相対射の族を coherent な変換空間への射として復元する。
方針：指定した標準表現を両端に保つ collage を分類し curry する。
規約：全パラメーターの始点・終点・底の条件を同時に保持する。
使われ方：比較射の右逆を作る普遍的な族への適用。 -/
lemma exists_coherentFamily_recovery {B K : SSet.{u + 1}}
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
  obtain ⟨⟨t, w⟩⟩ := transportRepresentationFamilyWitness_nonempty
    (leftUnstraighteningProjection_hasSmallSimplexFibers F)
    (leftUnstraighteningProjection_hasSmallSimplexFibers G)
    (unstraighteningTransportRepresentation F) (unstraighteningTransportRepresentation G) f hf
  exact ⟨t, w.prism, w.source, w.target, w.projection⟩


/-- 概要：小さい族の coherent な復元は一般の復元の特殊化。
方針：任意の底とパラメーターの復元定理を適用する。
規約：従来の小さい底の界面を保つ。
使われ方：小さい写像空間の比較。 -/
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
  exact exists_coherentFamily_recovery F G f hf

end SerrePositivity.InfinityCategories
