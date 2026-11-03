module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareCommonMap
public import SerrePositivity.InfinityCategories.Derived.DGNerveCommonMapZero
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorExact
public import SerrePositivity.InfinityCategories.Core.UniverseZeroTriangle
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence
/-!
概要：独立の係数圏宇宙を持つ全 dg 加群間の関手の共通 nerve は完全である。
方針：同じ標準 cone の実四角形像の普遍性を持ち上げ、全 cofiber 比較で移送する。
規約：全加群圏の Small 仮定は不要。既存の混在宇宙 cone 比較を再利用する。
使われ方：任意の加群値 dg 関手の混在宇宙の完全性における kernel tensor。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w t
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) (C : Type w)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]
  (F : DGFunctor R (RightModule R D) (RightModule R C))

lemma dgModuleFunctorCommon_cofiber_exists
    {x y : (dgModuleNerve R D) _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj (dgModuleNerve R D)) x y) :
    ∃ s : CofiberSquare f, IsPushoutSquare
      (uliftSquare.{max (u + 1) v, max (u + 1) v w t} s.square ≫
        dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) w, t} F) := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  change ∃ s : CofiberSquare (X := dgModuleNerve R D)
    (f : Truncated.Edge (Simplex.vertex M) (Simplex.vertex N)), _
  rw [← dgModuleEdge_edgeClosed R D f]
  refine ⟨dgModuleCofiberSquare R D (edgeClosed f), ?_⟩
  change IsPushoutSquare (uliftSquare (dgModuleConeSquare R D (edgeClosed f)) ≫ _)
  rw [← dgModuleConeSquareData_square, DGModuleSquareData.map_square_common]
  apply (isPushoutSquare_iff_ulift _).1
  exact (dgModuleConeSquare_isPushout R C (F.onClosed.map (edgeClosed f))).of_functorIso
    (dgModuleFunctorConeDataFunctorIso R D C F (edgeClosed f))

lemma dgModuleFunctorCommonNerve_isExactFunctor :
    IsExactFunctor (dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) w, t} F) where
  preservesZero := dgNerveCommonMap_preservesZeroVertices F
  preservesCofiber t ht := by
    let f := edgeOfSimplex (SSet.yonedaEquiv (squareBottomEdge ≫ t.down.square))
    let s : CofiberSquare f := {
      toZeroTriangle := t.down
      bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
      isPushout := t.isCofiber_down ht }
    obtain ⟨r, hr⟩ := dgModuleFunctorCommon_cofiber_exists R D C F f
    obtain ⟨e⟩ := nonempty_cofiberSquareFunctorIso r s
    have he := (e.ulift.{max (u + 1) v, max (u + 1) v w t}).precomp
      (uliftSquareIso.{max (u + 1) v, max (u + 1) v w t}).inv
    have hp := hr.of_functorIso (he.postcomp
      (dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) w, t} F))
    change IsPushoutSquare (uliftSquare t.down.square ≫ _) at hp
    rwa [t.ulift_down_square] at hp

end SerrePositivity.InfinityCategories
