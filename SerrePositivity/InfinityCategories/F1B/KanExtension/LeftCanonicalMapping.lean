module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.PrecompositionMappingPair
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCanonicalRestrictionHom
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialBoundaryCriterion

/-!
概要：標準左 Kan 関手から出る元の関手制限の写像空間の同値。
方針：標準局所余極限を全パラメータの定値族へ移し、指定 pinched 比較の判定を使う。
規約：相手の関手には Kan 条件を要求しない。
使われ方：元の左 Kan 関手の全部分圏からの制限の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：標準左 Kan 関手から出る元の制限の右 pinched 写像はホモトピー同値。
方針：定値パラメータ族の Hom 全単射を転置して全パラメータの判定へ渡す。
規約：δ の単射性は不要であり、G の局所普遍性も不要。
使われ方：元の Kan 関手全体からの制限の写像空間の主定理。 -/
lemma kanLeftCanonical_pinchedHomMap_equivalence {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, IsColimitCone (leftKanCanonicalCocone δ F c)) (G : C ⟶ D) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap ((pre δ).app D) (functorVertex F) (functorVertex G)) :=
  SerrePositivity.InfinityCategories.F1B.precomposition_pinchedHomMap_equivalence_of_constantFamily δ F G
    (fun A ↦ kanLeftCanonicalHomMap_constantFamily_bijective δ F hF
      (G ≫ constantFunctorMap A D))

/-- 概要：単射による制限は標準左 Kan 関手で始まる境界を充填する。
方針：全ての相手への指定 pinched 比較の同値を相対始対象の境界判定へ渡す。
規約：単射性は制限の inner fibration 性のためだけに使う。
使われ方：元の Kan 関手全体の制限からの境界固定の延長。 -/
lemma kanLeftCanonical_pre_initialBoundary {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [Mono δ] (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, IsColimitCone (leftKanCanonicalCocone δ F c)) :
    InitialBoundaryLifting ((pre δ).app D) (functorVertex F) := by
  apply (kanRelativeInitialVertex_iff_initialBoundary ((pre δ).app D) (functorVertex F)).1
  intro y
  obtain ⟨G, rfl⟩ := (functorVertexEquiv C D).surjective y
  exact kanLeftCanonical_pinchedHomMap_equivalence δ F hF G

end SerrePositivity.InfinityCategories.F1B
