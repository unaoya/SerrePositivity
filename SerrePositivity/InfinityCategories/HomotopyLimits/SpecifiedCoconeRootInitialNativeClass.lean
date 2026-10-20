module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootEndInitialProjection
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootEvaluationHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorIsoPostcompComposition

/-!
概要：評価固定の初期 Hom 円柱の底の類を、元の指定した初期射影比較の類へ同定する。
方針：三因子の底の相殺・右の raw な底の一致・評価上の忠実性を組み合わせる。
規約：底は同じ射の類として保持する。使われ方：共通 end 内の指定経路の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "I" => specifiedCoconeRootInitialComparisonIso hp p c hc dB dC y
local notation "HR" => specifiedCoconeRootEndInitialHomotopy hp p c hc dB dC y
local notation "H" => specifiedCoconeRootEvaluationHomotopy hp p c hc dB dC y
local notation "J" => specifiedCoconeRootInitialProjectionComparison hp p c hc dB dC y
local notation "P" => leftFibrationInitialProjection q c y
local notation "B" => Iso.hom (leftFibrationInitialBaseIso q c y)
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 三比較の合成同型の通常 Hom 表示での底は、元の初期射影比較の同じ射の類。 -/
lemma specifiedCoconeRootInitialComparisonIso_native_hom_arrow :
    Arrow.mk (FunctorIso.postcomp I (P ≫ B)).hom =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J)) := by
  have h := functorIso_postcomp_hom_arrow_map I (functorIsoOfSimplicialHomotopy HR) P B
    (specifiedCoconeRootInitialComparisonIso_base_hom_arrow hp p c hc dB dC y)
  refine h.trans ?_
  rw [homotopyIso_postcomp_hom]
  exact kanFunctorHomotopy_hom_arrow_of_h_eq (functorHomotopyPostcomp HR (P ≫ B)) J
    (specifiedCoconeRootEndInitialHomotopy_native_projection hp p c hc dB dC y)

/-- 厳密な評価固定代表の底も、元の指定した初期射影円柱の同じ射の類を持つ。 -/
lemma specifiedCoconeRootEvaluationHomotopy_native_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp H (P ≫ B)))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J)) := by
  have h := specifiedCoconeRootEvaluationHomotopy_hom hp p c hc dB dC y
  have hm := congrArg (hoFunctor.map ((ihom T).map (P ≫ B))).toFunctor.map h
  rw [← homotopyIso_postcomp_hom, functorIso_postcomp_hom]
  exact (congrArg Arrow.mk hm).trans
    (by simpa only [functorIso_postcomp_hom] using
      (specifiedCoconeRootInitialComparisonIso_native_hom_arrow hp p c hc dB dC y))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
