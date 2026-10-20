module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootInitialNativeClass
public import SerrePositivity.InfinityCategories.HomotopyLimits.EvaluationFixedHomotopyTriangle
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftRestrictionCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootedHomCylinder

/-!
概要：元の左・右の Hom 比較円柱と、指定した根辺の初期射影比較の合成則。
方針：評価固定の同じ三円柱を h Fun の忠実性で比較し、底へ写して指定類を照合する。
規約：既存の円柱の辺の類を保持。使われ方：共通 path end 内の左右の経路の整合性。
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
local notation "ev" => leftFibrationInitialEvaluation q c y
local notation "P" => leftFibrationInitialProjection q c y ≫
  Iso.hom (leftFibrationInitialBaseIso q c y)
local notation "z" => specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "H₀" => InitialEvaluationCylinder.homotopy
  (specifiedCoconeLeftHomCylinderData hp p c hc dB dC y)
local notation "H₁" => specifiedCoconeRootEvaluationHomotopy hp p c hc dB dC y
local notation "H₂" => InitialEvaluationCylinder.homotopy
  (specifiedCoconeRootedHomCylinder hp p c hc dB dC y)
local notation "J" => specifiedCoconeRootInitialProjectionComparison hp p c hc dB dC y
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 左円柱と元の初期射影比較の積は、同じ右円柱の辺の類である。 -/
lemma specifiedCoconeRootHomCylinder_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftHomCylinderComparison hp p c hc dB dC y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRootedHomCylinderComparison hp p c hc dB dC y)) := by
  have := leftFibrationInitialEvaluation_trivialKanFibration q c hc y
  have ht := evaluationFixedHomotopyTriangle_homMk_comp ev H₀ H₁ H₂ z
    (specifiedCoconeLeftHomCylinderData hp p c hc dB dC y).evaluation
    (specifiedCoconeRootEvaluationHomotopy_evaluation hp p c hc dB dC y)
    (specifiedCoconeRootedHomCylinder hp p c hc dB dC y).evaluation
  have h := congrArg (hoFunctor.map ((ihom T).map P)).toFunctor.map ht
  rw [(hoFunctor.map ((ihom T).map P)).toFunctor.map_comp,
    ← functorHomotopyPostcomp_hom H₀ P,
    ← functorHomotopyPostcomp_hom H₁ P, ← functorHomotopyPostcomp_hom H₂ P] at h
  have hJ := specifiedCoconeRootEvaluationHomotopy_native_hom_arrow hp p c hc dB dC y
  obtain ⟨_, _, hJ⟩ := (Arrow.mk_eq_mk_iff _ _).mp hJ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hJ
  rw [hJ] at h
  exact h

/-- 元の左右の円柱から同じ native 根辺へ至る二経路の射の類は厳密に一致する。 -/
lemma specifiedCoconeRootHomCylinder_native_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftHomCylinderComparison hp p c hc dB dC y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftRootNativeCylinder hp p c hc dB dC y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRootedHomCylinderComparison hp p c hc dB dC y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRootNativeCylinder hp p c hc dB dC y)) := by
  let L := SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (specifiedCoconeLeftHomCylinderComparison hp p c hc dB dC y))
  let M := SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J)
  let N := SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (specifiedCoconeRootNativeCylinder hp p c hc dB dC y))
  exact (congrArg (L ≫ ·)
      (specifiedCoconeRootFamilyTriangle_homMk_comp hp p c hc dB dC y).symm).trans
    ((Category.assoc L M N).symm.trans
      (congrArg (· ≫ N) (specifiedCoconeRootHomCylinder_homMk_comp hp p c hc dB dC y)))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
