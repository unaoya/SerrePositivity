module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFamilyTriangle
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftRootNativeCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootNativeCylinder

/-!
概要：左右の元の共通脚の全 Hom 族を、既存の native 比較円柱を二面に保って照合する。
方針：共通脚と終点係数の厳密な一致から、終点固定の全辺族の三角形を構成する。
規約：左右の比較円柱の raw な射と元の共通脚を保持する。
使われ方：指定輸送路の作用と左右の Hom 比較の合成を照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "e" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "L" => specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y
local notation "R" => specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y
local notation "P" => normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2))
  (specifiedCoconeNativeRootEdge_source hp p c hc dB dC) y ≫
    Iso.hom (leftFibrationInitialBaseIso q c y)

/-- 左右の元の全辺族の終点係数は、正規化前にも厳密に一致する。 -/
lemma specifiedCoconeRootFamilies_target :
    L ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
      R ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y := by
  have h := (specifiedCoconeLeftRootBaseEdgeFiberFamily_target hp p c hc dB dC y).trans
    (specifiedCoconeRootBaseEdgeFiberFamily_target hp p c hc dB dC y).symm
  simp only [normalizedCoconeRestrictionFiber_eq, ← Category.assoc] at h
  exact (cancel_mono _).mp h

local notation "hLR" => specifiedCoconeRootFamilies_target hp p c hc dB dC y

/-- 二つの元の切断比較を二面に保つ、同じ native 共通脚上の全 Hom の三角形。 -/
def specifiedCoconeRootFamilyTriangle := cosliceEdgeFamilyTriangle e y L R hLR

/-- 第一辺は、左三角形と右四面体の全辺族を結ぶ実際の円柱。 -/
def specifiedCoconeRootFamilyComparison : SSet.Homotopy L R :=
  cosliceEdgeFamilyComparison e y L R hLR

/-- 全辺族の比較は、終点係数を全時刻で固定する。 -/
lemma specifiedCoconeRootFamilyComparison_target :
    (specifiedCoconeRootFamilyComparison hp p c hc dB dC y).h ≫
        cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
      CartesianMonoidalCategory.fst T Δ[1] ≫ L ≫
        cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y :=
  cosliceEdgeFamilyComparison_target e y L R hLR

/-- 全辺族の同じ第一辺を、左右の既存の中間 Hom の始点射影として表示する。 -/
def specifiedCoconeRootInitialProjectionComparison : SSet.Homotopy
    (specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
      leftFibrationInitialProjection q c y ≫ (leftFibrationInitialBaseIso q c y).hom)
    (specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫
      leftFibrationInitialProjection q c y ≫ (leftFibrationInitialBaseIso q c y).hom) where
  h := (specifiedCoconeRootFamilyComparison hp p c hc dB dC y).h ≫ P
  h₀ := by
    refine ((Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ P)
      (specifiedCoconeRootFamilyComparison hp p c hc dB dC y).h₀)).trans ?_
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ (leftFibrationInitialBaseIso q c y).hom)
        (specifiedCoconeLeftRootBaseEdgeFiberFamily_source hp p c hc dB dC y))).trans
      (Category.assoc _ _ _)
  h₁ := by
    refine ((Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ P)
      (specifiedCoconeRootFamilyComparison hp p c hc dB dC y).h₁)).trans ?_
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ (leftFibrationInitialBaseIso q c y).hom)
        (specifiedCoconeRootBaseEdgeFiberFamily_source hp p c hc dB dC y))).trans
      (Category.assoc _ _ _)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 同じ三角形の第二面は、選択済みの右 native 比較円柱の射そのもの。 -/
lemma specifiedCoconeRootFamilyTriangle_second_projection :
    (T ◁ stdSimplex.δ (0 : Fin 3)) ≫
        ((specifiedCoconeRootFamilyTriangle hp p c hc dB dC y).family ≫ P) =
      (specifiedCoconeRootNativeCylinder hp p c hc dB dC y).h := by
  refine ((Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ P)
    (cosliceEdgeFamilyTriangle_second e y L R hLR))).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (specifiedCoconeRootNativeCylinder_projection hp p c hc dB dC y).symm

/-- 同じ三角形の対角面は、選択済みの左 native 比較円柱の射そのもの。 -/
lemma specifiedCoconeRootFamilyTriangle_diagonal_projection :
    (T ◁ stdSimplex.δ (1 : Fin 3)) ≫
        ((specifiedCoconeRootFamilyTriangle hp p c hc dB dC y).family ≫ P) =
      (specifiedCoconeLeftRootNativeCylinder hp p c hc dB dC y).h := by
  refine ((Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ P)
    (specifiedCoconeRootFamilyTriangle hp p c hc dB dC y).diagonal)).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (specifiedCoconeLeftRootNativeCylinder_projection hp p c hc dB dC y).symm

/-- 左右の native 比較の類は、実際の全辺族の第一辺で結ばれる。 -/
lemma specifiedCoconeRootFamilyTriangle_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRootInitialProjectionComparison hp p c hc dB dC y)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRootNativeCylinder hp p c hc dB dC y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftRootNativeCylinder hp p c hc dB dC y)) := by
  apply homotopyTriangle_homMk_comp _ _ _
    ((specifiedCoconeRootFamilyTriangle hp p c hc dB dC y).family ≫ P)
  · exact (Category.assoc _ _ _).symm
  · exact specifiedCoconeRootFamilyTriangle_second_projection hp p c hc dB dC y
  · exact specifiedCoconeRootFamilyTriangle_diagonal_projection hp p c hc dB dC y

/-- 同じ終点族を保つ指定経路の全辺族が得られれば、その類はこの第一辺に一意に一致する。 -/
lemma specifiedCoconeRootFamilyComparison_homMk_unique (K : SSet.Homotopy L R)
    (hK : K.h ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
      CartesianMonoidalCategory.fst T Δ[1] ≫ L ≫
        cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy K) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRootFamilyComparison hp p c hc dB dC y)) :=
  cosliceEdgeFamilyComparison_homMk_unique e y L R hLR K hK

end
end SerrePositivity.InfinityCategories.HomotopyLimits
