module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.UnstraighteningFamilyWitness
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.UnstraighteningFamilyComparison

/-!
概要：相対射の族を表す証拠をパラメーターで制限し普遍的な証拠を回収する。
方針：prism のパラメーター自然性を三条件へ同時に適用する。
規約：始点・終点・底をともに保持する。
使われ方：写像空間比較の左逆と普遍的な持ち上げの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：変換と相対射の族の証拠は任意のパラメーター制限を保つ。
方針：三つの条件に同じ制限射を前合成する。
規約：制限射の単射性や同値性は不要。
使われ方：復元した普遍的な証拠を変換空間へ制限する。 -/
def UnstraighteningFamilyWitness.comp {B K L : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} {t : K ⟶ leftUnstraighteningTransformationSpace F G}
    {f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G}
    (w : UnstraighteningFamilyWitness F G t f) (i : L ⟶ K) :
    UnstraighteningFamilyWitness F G (i ≫ t) ((leftUnstraightening F ◁ i) ≫ f) where
  prism := ((Δ[1] ⊗ leftUnstraightening F) ◁ i) ≫ w.prism
  source := by
    rw [← Category.assoc, prismEndpoint_parameter_naturality, Category.assoc, w.source,
      ← Category.assoc, whiskerLeft_fst]
  target := by
    rw [← Category.assoc, prismEndpoint_parameter_naturality, Category.assoc, w.target,
      ← Category.assoc]
  projection := by
    rw [Category.assoc, w.projection, ← Category.assoc]
    have hn : ((Δ[1] ⊗ leftUnstraightening F) ◁ i) ≫
        ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K) =
        ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ L) ≫ ((Δ[1] ⊗ B) ◁ i) := by
      apply SSet.hom_ext; intro n; rfl
    rw [hn, Category.assoc, ← functorParameterizedPrism_parameter,
      ← intervalMappingUncurry_precomp]

/-- 概要：写像空間比較の普遍的な持ち上げは恒等パラメーター族の実現の証拠。
方針：始点と射影の既存の公式と比較射の pointed な終点公式を束ねる。
規約：元の比較射そのものを使う。
使われ方：復元した左逆と元の変換空間の恒等射の比較。 -/
def unstraighteningUniversalFamilyWitness {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    UnstraighteningFamilyWitness F G (𝟙 (leftUnstraighteningTransformationSpace F G))
      (relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G)) where
  prism := leftUnstraighteningTransformationFamilyLift F G
  source := leftUnstraighteningTransformationFamilyLift_start F G
  target := (leftUnstraighteningMappingSpaceMap_pointed F G).symm
  projection := leftUnstraighteningTransformationFamilyLift_projection F G

end SerrePositivity.InfinityCategories
