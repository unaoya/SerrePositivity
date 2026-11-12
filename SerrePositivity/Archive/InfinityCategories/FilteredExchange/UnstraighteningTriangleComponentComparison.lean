module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningTriangleComparisonPresentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentTransport

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

/-- 元の全三角形比較の実際の成分を同じ長辺の始域付き比較の成分へ移す。 -/
lemma unstraighteningMappingTriangleIso_app_pre_heq_source {B K C : SSet.{u + 1}}
    [Quasicategory K]
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
      coherentTransformationFamilyDiagram c) (l : K _⦋0⦌) (s : C ⟶ leftUnstraightening F) :
    let f := relativeFunctorUncurry (a ≫ leftUnstraighteningMappingSpaceMap F G)
    let g := relativeFunctorUncurry (b ≫ leftUnstraighteningMappingSpaceMap G J)
    let h := lift f (snd (leftUnstraightening F) K) ≫ g
    let w := unstraighteningMappingTriangleLongWitness F G J a b c H h₀₁ h₁₂ h₀₂
    ∀ hh : h ≫ leftUnstraighteningProjection J =
        fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F,
    HEq
      (VertexIso.map ((unstraighteningMappingTriangleIso F G J a b c H h₀₁ h₁₂ h₀₂).app l)
        (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) s))
      (VertexIso.map
        ((unstraighteningSourceFamilyComparisonIso F J (leftUnstraighteningProjection F)
          (𝟙 (leftUnstraightening F)) (Category.id_comp _) c h hh
          w.prism w.source w.target w.projection).app l)
        (relativeFunctorPre (leftUnstraighteningProjection J)
          (leftUnstraighteningProjection F) s)) := by
  dsimp only
  intro hh
  let e := unstraighteningMappingTriangleIso F G J a b c H h₀₁ h₁₂ h₀₂
  let w := unstraighteningMappingTriangleLongWitness F G J a b c H h₀₁ h₁₂ h₀₂
  let h := lift (relativeFunctorUncurry (a ≫ leftUnstraighteningMappingSpaceMap F G))
    (snd (leftUnstraightening F) K) ≫
      relativeFunctorUncurry (b ≫ leftUnstraighteningMappingSpaceMap G J)
  let e' := unstraighteningSourceFamilyComparisonIso F J (leftUnstraighteningProjection F)
    (𝟙 (leftUnstraightening F)) (Category.id_comp _) c h hh
    w.prism w.source w.target w.projection
  have hs : (c ≫ leftUnstraighteningMappingSpaceMap F J) ≫
      relativeFunctorOverPre (leftUnstraighteningProjection J)
        (Over.homMk (U := Over.mk (leftUnstraighteningProjection F))
          (V := Over.mk (leftUnstraighteningProjection F))
          (𝟙 (leftUnstraightening F)) (Category.id_comp _)) =
      c ≫ leftUnstraighteningMappingSpaceMap F J := by
    change _ ≫ relativeFunctorOverPre _ (𝟙 _) = _
    rw [relativeFunctorOverPre_id, Category.comp_id]
  have hc : relativeFunctorCurry h hh =
      lift (a ≫ leftUnstraighteningMappingSpaceMap F G)
        (b ≫ leftUnstraighteningMappingSpaceMap G J) ≫
          relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
            (Over.mk (leftUnstraighteningProjection G))
            (Over.mk (leftUnstraighteningProjection J)) := by
    apply relativeFunctorUncurry_injective
    rw [relativeFunctorUncurry_curry]
    apply SSet.hom_ext
    intro n
    rfl
  have he := functorIso_app_heq_of_heq e e' hs.symm hc.symm
    (unstraighteningMappingTriangleIso_heq_source F G J a b c H h₀₁ h₁₂ h₀₂ hh) l
  exact vertexIso_map_heq_of_heq (e.app l) (e'.app l)
    (congrArg (fun k => k.app (Opposite.op ⦋0⦌) l) hs.symm)
    (congrArg (fun k => k.app (Opposite.op ⦋0⦌) l) hc.symm) he
    (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) s)

end SerrePositivity.InfinityCategories.F2
