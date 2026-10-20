module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeNativeBaseTerminal
public import SerrePositivity.InfinityCategories.HomotopyLimits.SimplexTerminalCosliceFiber

/-!
概要：元の rooted 全族と native 普遍全族を、同じ全 Hom の終端係数を保って比較する。
方針：同じパラメータ・点図式の厳密な式から、最後の頂点制限の自明 Kan fiber で結ぶ。
規約：最後の頂点を全時刻固定し、付加辺の終端固定までは仮定しない。
使われ方：同じ全族間円柱の二面を用いた native 指定経路の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "T" => pinchedHomLeft (JoinCocone.vertex d) y
local notation "Q" => Iso.inv (leftFibrationInitialBaseIso (sliceUnderProjection p) d y)

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "v" => stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)
local notation "ht" => specifiedCoconeLeftUniversalNative_tip hp p c hc dB dC
local notation "R" => normalizedCoconeRestrictionFiber σ v ht y
local notation "N" => specifiedCoconeLeftNativeBaseDiagramFamily hp p c hc dB dC y
local notation "U" => specifiedCoconeLeftUniversalNativeFamily hp p c hc dB dC y

/-- 元の左 rooted 全族と native 普遍全族は、同じ全 Hom の終端上で結べる。 -/
lemma exists_specifiedCoconeLeftNativeUniversalComparison :
    ∃ H : SSet.Homotopy N U, H.h ≫ R = fst T Δ[1] ≫ Q := by
  have := normalizedCoconeRestrictionFiber_of_rightAnodyne σ v triangleTerminalVertex_rightAnodyne
    (coconeVertexDiagram d) ht y
  have he : N ≫ R = U ≫ R :=
    (specifiedCoconeLeftNativeBaseDiagramFamily_terminal hp p c hc dB dC y).trans
      (specifiedCoconeLeftUniversalNativeFamily_terminal hp p c hc dB dC y).symm
  obtain ⟨H, hH⟩ := exists_homotopy_over_trivialKanFibration R N U he
  refine ⟨H, ?_⟩
  exact hH.trans (congrArg (fst T Δ[1] ≫ ·)
    (specifiedCoconeLeftUniversalNativeFamily_terminal hp p c hc dB dC y))

/-- 同じ左の実際の全族を、最後の頂点を全時刻固定する一つの円柱で結ぶ。 -/
def specifiedCoconeLeftNativeUniversalComparison : SSet.Homotopy N U :=
  (exists_specifiedCoconeLeftNativeUniversalComparison hp p c hc dB dC y).choose

/-- 全族間の同じ比較円柱は、元の全 Hom の終端係数を全時刻固定する。 -/
lemma specifiedCoconeLeftNativeUniversalComparison_terminal :
    (specifiedCoconeLeftNativeUniversalComparison hp p c hc dB dC y).h ≫ R = fst T Δ[1] ≫ Q :=
  (exists_specifiedCoconeLeftNativeUniversalComparison hp p c hc dB dC y).choose_spec
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "v" => (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
  stdSimplex.δ (0 : Fin 4)
local notation "ht" => specifiedCoconeRightUniversalNative_tip hp p c hc dB dC
local notation "R" => normalizedCoconeRestrictionFiber σ v ht y
local notation "N" => specifiedCoconeRightNativeBaseDiagramFamily hp p c hc dB dC y
local notation "U" => specifiedCoconeRightUniversalNativeFamily hp p c hc dB dC y

/-- 元の右 rooted 全族と native 普遍全族は、同じ全 Hom の終端上で結べる。 -/
lemma exists_specifiedCoconeRightNativeUniversalComparison :
    ∃ H : SSet.Homotopy N U, H.h ≫ R = fst T Δ[1] ≫ Q := by
  have := normalizedCoconeRestrictionFiber_of_rightAnodyne σ v
    tetrahedronTerminalVertex_rightAnodyne
    (coconeVertexDiagram d) ht y
  have he : N ≫ R = U ≫ R :=
    (specifiedCoconeRightNativeBaseDiagramFamily_terminal hp p c hc dB dC y).trans
      (specifiedCoconeRightUniversalNativeFamily_terminal hp p c hc dB dC y).symm
  obtain ⟨H, hH⟩ := exists_homotopy_over_trivialKanFibration R N U he
  refine ⟨H, ?_⟩
  exact hH.trans (congrArg (fst T Δ[1] ≫ ·)
    (specifiedCoconeRightUniversalNativeFamily_terminal hp p c hc dB dC y))

/-- 同じ右の実際の全族を、最後の頂点を全時刻固定する一つの円柱で結ぶ。 -/
def specifiedCoconeRightNativeUniversalComparison : SSet.Homotopy N U :=
  (exists_specifiedCoconeRightNativeUniversalComparison hp p c hc dB dC y).choose

/-- 全族間の同じ比較円柱は、元の全 Hom の終端係数を全時刻固定する。 -/
lemma specifiedCoconeRightNativeUniversalComparison_terminal :
    (specifiedCoconeRightNativeUniversalComparison hp p c hc dB dC y).h ≫ R = fst T Δ[1] ≫ Q :=
  (exists_specifiedCoconeRightNativeUniversalComparison hp p c hc dB dC y).choose_spec
end

end
end SerrePositivity.InfinityCategories.HomotopyLimits
