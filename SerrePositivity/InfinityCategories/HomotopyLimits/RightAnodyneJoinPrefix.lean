module

public import SerrePositivity.InfinityCategories.F1.Joins.JoinLeftBoundaryAnodyne
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLongEdge
public import SerrePositivity.InfinityCategories.Core.JoinSimplexFaces

/-!
概要：終点を含む join の面の right anodyne 性を証明する。
方針：相対 join 境界へ pushout で入り、その inner anodyne な包含へ続ける。
規約：モデル構造を使わず right fibration に対する持ち上げ性で扱う。
使われ方：右修正三角形に始対象からの比較辺を前置した四面体の、終端三角形への相対制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- right anodyne な単射は、右に任意の形状を join しても right anodyne。 -/
lemma joinMap_rightAnodyne {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (K : SSet.{u}) (hi : rightAnodyneExtensions i) :
    rightAnodyneExtensions (joinMap i (𝟙 K)) := by
  have h₀ : rightAnodyneExtensions (pushout.inl (joinInl A K) i) :=
    MorphismProperty.of_isPushout (IsPushout.of_hasPushout (joinInl A K) i) hi
  have h₁ : rightAnodyneExtensions (joinLeftBoundaryMap i K) := by
    intro X Y q hq
    have : RightFibration q := ⟨hq⟩
    exact (joinLeftBoundaryMap_innerAnodyne_of_rightAnodyne i K hi) q InnerFibration.mem
  have h := rightAnodyneExtensions.comp_mem _ _ h₀ h₁
  rwa [joinLeftBoundaryMap_join] at h

/-- 二つの辺の join で最初の頂点を除くと、終端三角形への包含になる。 -/
lemma joinEdgeEdge_terminalFace :
    joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (Δ[1] : SSet.{u})) ≫
        (joinStdSimplexIso 1 1).hom =
      (joinStdSimplexIso 0 1).hom ≫ stdSimplex.δ (0 : Fin 4) := by
  simpa only [show (0 : Fin 2).castAdd 2 = (0 : Fin 4) from rfl] using
    DGNerve.joinStdSimplexIso_left_face 0 (0 : Fin 2)

/-- 四面体の終端三角形の包含は right anodyne。 -/
lemma tetrahedronTerminalFace_rightAnodyne :
    rightAnodyneExtensions (stdSimplex.δ (0 : Fin 4) : (Δ[2] : SSet.{u}) ⟶ Δ[3]) := by
  have h := joinMap_rightAnodyne (stdSimplex.δ (0 : Fin 2))
    (Δ[1] : SSet.{u}) endpointInclusion_rightAnodyne
  have h' := rightAnodyneExtensions.comp_mem _ (joinStdSimplexIso 1 1).hom h
    (MorphismProperty.llp_of_isIso _ _)
  rw [joinEdgeEdge_terminalFace] at h'
  exact (rightAnodyneExtensions.cancel_left_of_respectsIso (joinStdSimplexIso 0 1).hom _).mp h'

end SerrePositivity.InfinityCategories.HomotopyLimits
