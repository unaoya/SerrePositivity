module

public import SerrePositivity.KST.Spectra.SkeletalPathCoboundary

/-!
概要：path 空間での骨格延長の終点の値を、元の loop cochain の正規化交代微分で計算する。
方針：セルの各面の厳密な一致を球面的 path 境界の式へ代入する。
規約：セル次元は n+3、符号は (-1)^(n+3)。実際の成分接続写像との比較は別に保持する。
使われ方：Goerss–Jardine VIII §1。交代和と幾何的な coboundary の値の照合。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalPathCoboundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：正規化微分を loop 群同型で移すと、延長の終点のセルの値を符号付きで得る。
方針：幾何的なセルの path を相対球面的境界として読み、既存の交代微分の式へ合成する。
規約：任意の path 延長で値を計算し、充填の存在を仮定するだけの結論にしない。
使われ方：Goerss–Jardine VIII §1。成分微分の代表と照合すべき交代式。 -/
theorem normalizedDifferential_endpoint (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] {n : ℕ}
    (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
    (hf : ∀ t : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌,
      yonedaEquiv.symm t ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (H : (K.skeleton (n + 4) : SSet.{u}) ⟶ (basedPathSpace Y).right)
    (hH : UnbasedPointedMapping.skeletalInclusion K (n + 2) ≫ H =
      f ≫ (PointedMapping.loopToPath Y).right)
    (s : K.nonDegenerate (n + 3)) :
    (loopPositiveHomotopyEquiv Y (n + 1)).toAdditive
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
          (AddCommGrpCat.of (Additive
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right (n + 1) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)))
          (n + 2) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f hf) s) =
      (-1 : ℤ) ^ (n + 3) • Additive.ofMul
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (endpointSimplex K Y f H hH s.val)) := by
  let b := SimplexBasepoint.rebase (pathEndpoint_basepoint Y).symm
    (endpointSimplex K Y f H hH s.val)
  let a := fun j : Fin (n + 4) ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f hf (K.δ j s.val)
  have hface : ∀ j, stdSimplex.δ j ≫ cellPath K Y H s.val =
      (a j).map ≫ (loopBasedPathFiberIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Y).right
        ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) := by
    intro j
    rw [PointedMapping.loopToPath_fiber]
    exact cellPath_face K Y f H hH hf s.val j
  have h := SphericalPathBoundary.alternating_loopPositive Y b a
    (cellPath K Y H s.val) (cellPath_endpoint K Y f H hH s.val) hface
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 2) (Iso.refl Y.right)
      (pathEndpoint_basepoint Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (endpointSimplex K Y f H hH s.val) := by
    rw [SimplexBasepoint.group_mk]
    congr 1
  rw [hb] at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.differential_cochain_apply]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass,
    map_sum, map_zsmul, MulEquiv.toAdditive_apply_apply, toMul_ofMul] using h

/-- 概要：正規化微分は、path 延長の終点の実際の fiber 成分の係数を計算する。
方針：幾何的なセルの path を相対球面的境界として読み、既存の交代微分の式へ合成する。
規約：任意の path 延長で値を計算し、充填の存在を仮定するだけの結論にしない。
使われ方：Goerss–Jardine VIII §1。成分微分の代表と照合すべき交代式。 -/
theorem normalizedDifferential_endpointFiber (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] {n : ℕ}
    (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
    (hf : ∀ t : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌,
      yonedaEquiv.symm t ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (H : (K.skeleton (n + 4) : SSet.{u}) ⟶ (basedPathSpace Y).right)
    (hH : UnbasedPointedMapping.skeletalInclusion K (n + 2) ≫ H =
      f ≫ (PointedMapping.loopToPath Y).right)
    (s : K.nonDegenerate (n + 3)) :
    (loopPositiveHomotopyEquiv Y (n + 1)).toAdditive
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
          (AddCommGrpCat.of (Additive
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right (n + 1) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)))
          (n + 2) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f hf) s) =
      (-1 : ℤ) ^ (n + 3) • Additive.ofMul
        (SkeletalCellAttachment.stageFiberComponentEquiv K Y (n + 2)
          (π₀.mk (endpointFiberVertex K Y f H hH)) s) := by
  rw [endpointFiberVertex_coefficient]
  exact normalizedDifferential_endpoint K Y f hf H hH s

end
end SerrePositivity.KST.Spectra.SkeletalPathCoboundary
