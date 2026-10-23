module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningTriangleComponentComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningIdentityComparisonRestriction

/-!
概要：元の全三角形比較の各点成分を同じ二 prism の延長空間の比較へ制限する。
方針：実際の成分の端点正規化を外し、元の長辺の証拠へ制限公式を適用する。
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

/-- 元の全三角形の指定比較成分は、同じ二 prism の制限後の指定終点比較。 -/
lemma unstraighteningMappingTriangleIso_app_pre {B K C : SSet.{u + 1}}
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
    let w := unstraighteningMappingTriangleLongWitness F G J a b c H h₀₁ h₁₂ h₀₂
    HEq
      (VertexIso.map ((unstraighteningMappingTriangleIso F G J a b c H h₀₁ h₁₂ h₀₂).app l)
        (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) s))
      (unstraighteningIdentityRestrictedEndpointIso F J c
        w.prism w.source w.projection l s) := by
  dsimp only
  have hh := unstraighteningMappingComposite_projection F G J a b
  have he := unstraighteningMappingTriangleIso_app_pre_heq_source F G J a b c
    H h₀₁ h₁₂ h₀₂ l s hh
  exact he.trans (unstraighteningIdentityComparisonIso_app_pre F J c _ hh
    (unstraighteningMappingTriangleLongWitness F G J a b c H h₀₁ h₁₂ h₀₂).prism
    (unstraighteningMappingTriangleLongWitness F G J a b c H h₀₁ h₁₂ h₀₂).source
    (unstraighteningMappingTriangleLongWitness F G J a b c H h₀₁ h₁₂ h₀₂).target
    (unstraighteningMappingTriangleLongWitness F G J a b c H h₀₁ h₁₂ h₀₂).projection l s)

end SerrePositivity.InfinityCategories.F2
