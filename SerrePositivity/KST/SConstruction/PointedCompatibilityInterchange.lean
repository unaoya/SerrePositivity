module
public import SerrePositivity.KST.SConstruction.FamilyChainInterchangeSquares
public import SerrePositivity.KST.SConstruction.PointedFamilyConstantComposition
public import SerrePositivity.KST.Spectra.SuspensionComposition

/-! # 補正列の suspension と元の適合円柱の区間交換
概要：suspension した全補正区間と、定数な二合成間の適合円柱の交換を実正方形で構成する。
方針：元の二時刻の構成へ豊穣合成を適用し、二つの水平面を通常の後合成へ計算する。
規約：元の適合円柱と補正全区間を保持する。
使われ方：K 合成補正の構造射での射影を元の構造適合と照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra Spectra.PointedMapping
open scoped Simplicial
local instance pointedCompatibilityInterchangeSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {U : SSet.{u}} {A R C : PointedSimplicialSet.{u}}
  {a b : U ⟶ (PointedObject.basedHom A R).right}
  (c : FamilyHomotopyChain a b) (d₀ d₁ : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension R ⟶ C)
  (H : SSet.Homotopy (SSet.const (X := U) (familyVertex d₀)) (SSet.const (familyVertex d₁)))

/-- suspension した元の補正全区間と同じ適合円柱との実交換正方形列。 -/
def pointedCompatibilityInterchangeSquares :
    List ((U ⊗ (Δ[1] : SSet.{u})) ⊗ (Δ[1] : SSet.{u}) ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) C).right) :=
  familyHomotopyChainInterchangeSquares
    (familyHomotopyChainMap c ((suspensionHom A R).right)) H.h
    (eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension R) C)

/-- 第二時刻の零面は元の補正の suspension と適合の始点の後合成を回収する。 -/
lemma pointedCompatibilityInterchangeSquares_second_zero :
    (pointedCompatibilityInterchangeSquares c d₀ d₁ H).map (SSet.ι₀ ≫ ·) =
      (familyHomotopyChainTrace c).map (fun h => h ≫ (suspensionHom A R).right ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) d₀).right) := by
  simp only [pointedCompatibilityInterchangeSquares,
    familyHomotopyChainInterchangeSquares_second_zero, familyHomotopyChainMap_trace,
    List.map_map, Function.comp_def]
  congr 1
  funext h
  rw [H.h₀, SSet.comp_const, pointedFamilyComposition_const_right]
  rfl

/-- 第二時刻の一面は元の補正の suspension と適合の終点の後合成を回収する。 -/
lemma pointedCompatibilityInterchangeSquares_second_one :
    (pointedCompatibilityInterchangeSquares c d₀ d₁ H).map (SSet.ι₁ ≫ ·) =
      (familyHomotopyChainTrace c).map (fun h => h ≫ (suspensionHom A R).right ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension A) d₁).right) := by
  simp only [pointedCompatibilityInterchangeSquares,
    familyHomotopyChainInterchangeSquares_second_one, familyHomotopyChainMap_trace,
    List.map_map, Function.comp_def]
  congr 1
  funext h
  rw [H.h₁, SSet.comp_const, pointedFamilyComposition_const_right]
  rfl

end SerrePositivity.KST.SConstruction
