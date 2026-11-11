module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianTriangleMiddleRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Composition
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：三角形の最初の辺と長辺が cocartesian なら後半の辺も cocartesian。
方針：真ん中の頂点への相対制限から、後半の辺への制限を消去する。
規約：射は inner fibration、底は quasicategory。
使われ方：最終 fiber への輸送が cocartesian 辺を可逆辺へ送ることの検証。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：三角形の後半の辺の包含は右 anodyne。
方針：最初の辺の終点を貼り、内ホーンを充填する。
規約：後半の辺は δ₀ で指定する。
使われ方：三角形から後半の辺への相対 coslice 制限の充填。 -/
lemma triangleSecondEdge_rightAnodyne :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) := by
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (horn₂₁.ι₁₂ : (Δ[1] : SSet.{u}) ⟶ Λ[2, 1]) :=
    MorphismProperty.of_isPushout horn₂₁.isPushout.flip _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.endpointInclusion_rightAnodyne
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions_horn (1 : Fin 3) (by decide)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.comp_mem horn₂₁.ι₁₂ (horn 2 1).ι h₁ h₂
  rwa [horn.ι_ι] at h

/-- 概要：後半の辺の像の包含は右 anodyne。
方針：辺の標準単体による表示同型を除く。
規約：零頂点を除いた面。
使われ方：部分複体に沿う制限の定理を適用する。 -/
lemma triangleSecondFace_rightAnodyne :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (stdSimplex.face (n := 2) {(0 : Fin 3)}ᶜ).ι := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.cancel_left_of_respectsIso
    (stdSimplex.faceSingletonComplIso (0 : Fin 3)).hom]
  rw [stdSimplex.faceSingletonComplIso_hom_ι]
  exact triangleSecondEdge_rightAnodyne

/-- 概要：inner fibration の三角形から後半の辺への相対制限は trivial Kan fibration。
方針：後半の辺の包含の右 anodyne 性を使う。
規約：三角形の辺の cocartesian 性は不要。
使われ方：相対制限の合成からの消去。 -/
lemma relativeCosliceRestriction_triangleSecondEdge {X Y : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction t q (stdSimplex.δ (0 : Fin 3))) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_trivialKanFibration_of_rightAnodyne t q
    (stdSimplex.face {(0 : Fin 3)}ᶜ) triangleSecondFace_rightAnodyne
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceRestriction_trivialKanFibration_subcomplexIso t q
    (stdSimplex.face {(0 : Fin 3)}ᶜ) (stdSimplex.faceSingletonComplIso (0 : Fin 3))
  simpa only [stdSimplex.faceSingletonComplIso_hom_ι] using h

/-- 概要：底の三角形から後半の辺への coslice 制限は trivial Kan fibration。
方針：部分複体への制限の充填性を辺の標準表示へ移す。
規約：値域は quasicategory。
使われ方：相対制限の消去に必要な底の充填性。 -/
lemma sliceUnderRestrict_triangleSecondEdge {Y : SSet.{u}} [Quasicategory Y]
    (t : (Δ[2] : SSet.{u}) ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t (stdSimplex.δ (0 : Fin 3))) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration_of_rightAnodyne t
    (stdSimplex.face {(0 : Fin 3)}ᶜ) triangleSecondFace_rightAnodyne
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration_subcomplexIso t
    (stdSimplex.face {(0 : Fin 3)}ᶜ) (stdSimplex.faceSingletonComplIso (0 : Fin 3))
  simpa only [stdSimplex.faceSingletonComplIso_hom_ι] using h

/-- 概要：最初の辺と長辺が cocartesian なら三角形の後半の辺も cocartesian。
方針：真ん中の頂点への相対制限から後半の辺への制限を消去する。
規約：底は quasicategory、射は inner fibration。
使われ方：Kerodon Corollary 5.1.2.4（Tag 01TS） の cocartesian 側の消去方向。 -/
@[kerodon 01TS]
lemma isCocartesianEdge_triangle_second_of_first_long {X Y : SSet.{u}} [Quasicategory Y]
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t)))
    (hh : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ t))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction_middle t q hf hh
  have hv : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (2 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [hv] at h
  have := h
  have := relativeCosliceRestriction_triangleSecondEdge t q
  have := sliceUnderRestrict_triangleSecondEdge (t ≫ q)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction_trivialKanFibration_cancel t q
    (stdSimplex.δ (0 : Fin 3)) (stdSimplex.δ (1 : Fin 2))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_relativeCosliceRestriction_source (stdSimplex.δ (0 : Fin 3) ≫ t) q

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
