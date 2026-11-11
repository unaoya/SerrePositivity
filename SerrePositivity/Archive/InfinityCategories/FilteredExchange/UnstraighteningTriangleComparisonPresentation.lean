module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningTriangleComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningSourceComparisonPresentation

/-!
概要：指定三角形の長辺の unstraightening 比較は、二辺の実際の相対合成と同型。
方針：元の全三角形の持ち上げの長辺から証拠を取り、その証拠の比較を直接使う。
規約：全 Hom のパラメータを保持し、点ごとの合成則に弱めない。
使われ方：一般 coherent 余錐の全 Hom の比較の合成整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二つの族の実際の合成は元の始域の射影を被覆する。 -/
lemma unstraighteningMappingComposite_projection {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (a : K ⟶ leftUnstraighteningTransformationSpace F G)
    (b : K ⟶ leftUnstraighteningTransformationSpace G J) :
    (lift (relativeFunctorUncurry (a ≫ leftUnstraighteningMappingSpaceMap F G))
      (snd (leftUnstraightening F) K) ≫
        relativeFunctorUncurry (b ≫ leftUnstraighteningMappingSpaceMap G J)) ≫
          leftUnstraighteningProjection J =
      fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F := by
  let d := lift (a ≫ leftUnstraighteningMappingSpaceMap F G)
    (b ≫ leftUnstraighteningMappingSpaceMap G J) ≫
      relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
        (Over.mk (leftUnstraighteningProjection G)) (Over.mk (leftUnstraighteningProjection J))
  have hd : relativeFunctorUncurry d =
      lift (relativeFunctorUncurry (a ≫ leftUnstraighteningMappingSpaceMap F G))
        (snd (leftUnstraightening F) K) ≫
          relativeFunctorUncurry (b ≫ leftUnstraighteningMappingSpaceMap G J) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← hd]
  exact relativeFunctorUncurry_projection d

/-- 実際の三角形比較は元の全 pointed 三角形の同じ長辺の始域付き比較の端点正規化。 -/
lemma unstraighteningMappingTriangleIso_heq_source {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (a : K ⟶ leftUnstraighteningTransformationSpace F G)
    (b : K ⟶ leftUnstraighteningTransformationSpace G J)
    (c : K ⟶ leftUnstraighteningTransformationSpace F J)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram a)
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram b)
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram c) :
    let f := relativeFunctorUncurry (a ≫ leftUnstraighteningMappingSpaceMap F G)
    let g := relativeFunctorUncurry (b ≫ leftUnstraighteningMappingSpaceMap G J)
    let h := lift f (snd (leftUnstraightening F) K) ≫ g
    let w := unstraighteningMappingTriangleLongWitness F G J a b c H h₀₁ h₁₂ h₀₂
    ∀ hh : h ≫ leftUnstraighteningProjection J =
        fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F,
    HEq (unstraighteningMappingTriangleIso F G J a b c H h₀₁ h₁₂ h₀₂)
      (unstraighteningSourceFamilyComparisonIso F J (leftUnstraighteningProjection F)
        (𝟙 (leftUnstraightening F)) (Category.id_comp _) c h hh
        w.prism w.source w.target w.projection) := by
  dsimp only
  intro hh
  unfold unstraighteningMappingTriangleIso
  dsimp only
  exact iso_endpoints_heq _ _ _

end SerrePositivity.InfinityCategories.F2
