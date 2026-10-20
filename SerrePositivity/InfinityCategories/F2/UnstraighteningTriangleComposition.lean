module

public import SerrePositivity.InfinityCategories.F2.UnstraighteningMappingTrianglePrism
public import SerrePositivity.InfinityCategories.F2.UnstraighteningTriangleWitness
public import SerrePositivity.InfinityCategories.F1.UnstraighteningFamilyComparison
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorComposition

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

/-- 概要：任意の指定三角形上で比較射は二辺の合成を長辺の像へ移す。
方針：元の全二単体の持ち上げを保持し、その長辺の終点を直接比較する。
規約：三辺も三角形も選び直さない。使われ方：余錐の合成を全空間へ移す。 -/
def unstraighteningMappingTriangleIso {B K : SSet.{u + 1}}
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
    FunctorIso (c ≫ leftUnstraighteningMappingSpaceMap F J)
      (lift (a ≫ leftUnstraighteningMappingSpaceMap F G)
        (b ≫ leftUnstraighteningMappingSpaceMap G J) ≫
          relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
            (Over.mk (leftUnstraighteningProjection G))
            (Over.mk (leftUnstraighteningProjection J))) := by
  let f := relativeFunctorUncurry (a ≫ leftUnstraighteningMappingSpaceMap F G)
  let g := relativeFunctorUncurry (b ≫ leftUnstraighteningMappingSpaceMap G J)
  let w := unstraighteningMappingTriangleLongWitness F G J a b c H h₀₁ h₁₂ h₀₂
  let d := lift (a ≫ leftUnstraighteningMappingSpaceMap F G)
    (b ≫ leftUnstraighteningMappingSpaceMap G J) ≫
      relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
        (Over.mk (leftUnstraighteningProjection G)) (Over.mk (leftUnstraighteningProjection J))
  have hd : relativeFunctorUncurry d = lift f (snd (leftUnstraightening F) K) ≫ g := by
    apply SSet.hom_ext
    intro n
    rfl
  have wd : UnstraighteningFamilyWitness F J c (relativeFunctorUncurry d) := by
    rw [hd]
    exact w
  have e := unstraighteningFamilyComparisonIso F J c (relativeFunctorUncurry d)
    (relativeFunctorUncurry_projection d) wd.prism wd.source wd.target wd.projection
  have hc : relativeFunctorCurry (relativeFunctorUncurry d)
      (relativeFunctorUncurry_projection d) = d := by
    apply relativeFunctorUncurry_injective
    exact relativeFunctorUncurry_curry _ _
  rw [hc] at e
  exact e

/-- 概要：任意の二つの変換の族の合成は、相対写像空間の実際の合成と整合する。
方針：全パラメータの三角形を充填し、指定三角形の比較を適用する。
規約：底やパラメータの小ささは不要。使われ方：全 Hom の合成則。 -/
lemma unstraighteningMappingCompositionFamily {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (a : K ⟶ leftUnstraighteningTransformationSpace F G)
    (b : K ⟶ leftUnstraighteningTransformationSpace G J) :
    ∃ c : K ⟶ leftUnstraighteningTransformationSpace F J,
      Nonempty (FunctorIso (c ≫ leftUnstraighteningMappingSpaceMap F J)
        (lift (a ≫ leftUnstraighteningMappingSpaceMap F G)
          (b ≫ leftUnstraighteningMappingSpaceMap G J) ≫
            relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
              (Over.mk (leftUnstraighteningProjection G))
              (Over.mk (leftUnstraighteningProjection J)))) := by
  obtain ⟨c, H, h₀₁, h₁₂, h₀₂⟩ := coherentTransformationFamilyTriangle_nonempty a b
  exact ⟨c, ⟨unstraighteningMappingTriangleIso F G J a b c H h₀₁ h₁₂ h₀₂⟩⟩

end SerrePositivity.InfinityCategories.F2
