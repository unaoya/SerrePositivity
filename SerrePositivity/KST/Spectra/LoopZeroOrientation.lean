module

public import SerrePositivity.KST.Spectra.PathVertexContraction
public import SerrePositivity.KST.Spectra.LoopPathVertices
public import SerrePositivity.KST.Spectra.LoopZeroPenultimate
public import SerrePositivity.KST.Spectra.LoopBoundaryRepresentatives
public import SerrePositivity.KST.Spectra.SphereMappingComponents

/-!
概要：通常の円の成分表示と path の連結射で定めた零 loop 同値の向き。
方針：円からの射の path を収縮し、終点が元の辺であることを逆元公式へ代入する。
規約：circle と interval の向きを固定し、両比較の相違を群の逆元で明示する。
使われ方：Goerss–Jardine I §7–8、VIII §1。骨格の成分微分と既存係数の符号の比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：円からの射の零 loop 同値の値は、元の辺の基本群の類の逆元。
方針：その path の収縮の辺に零 loop の最後から二番目の面の公式を適用する。
規約：向きは二端点を潰す標準商のまま保持する。
使われ方：Goerss–Jardine I §8。零 loop 同値の符号の代表での検査。 -/
theorem loopZeroHomotopyEquiv_familyVertex (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (f : PointedSimplicialSet.circle.{u} ⟶ Y) :
    loopZeroHomotopyEquiv Y
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 ((PtSimplex.equiv₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint).symm
          (PointedMapping.familyVertex f))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv Y 1 f))⁻¹ := by
  let a := (PtSimplex.equiv₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint).symm (PointedMapping.familyVertex f)
  let v := (PointedMapping.loopToPath Y).right.app _ (PointedMapping.familyVertex f)
  let s := SimplexBasepoint.rebase (pathEndpoint_basepoint Y).symm (SphereSimplex.equiv Y 1 f)
  have hT : pathVertexContraction Y v ≫ (pathEndpoint Y).right = s.map := by
    rw [pathVertexContraction_endpoint]
    change (PointedMapping.familyMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y v).right =
      (SphereSimplex.equiv Y 1 f).map
    dsimp only [v]
    rw [loopToPath_familyVertex, PointedMapping.familyMap_familyVertex]
    change circleIntervalProjection.right ≫ f.right =
      PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫ f.right
    rw [circleIntervalProjection_right]
  have h₀ : stdSimplex.δ (0 : Fin 2) ≫ pathVertexContraction Y v =
      a.map ≫ (PointedMapping.loopToPath Y).right := by
    rw [pathVertexContraction_face_zero, a.map_eq_const_equiv₀, const_comp]
    simp only [a, Equiv.apply_symm_apply]
    rfl
  have h := loopZero_penultimate Y s a (pathVertexContraction Y v) hT h₀
    (pathVertexContraction_face_one Y v)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl Y.right) (pathEndpoint_basepoint Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv Y 1 f) := by
    rw [SimplexBasepoint.group_mk]
    congr 1
  rw [hs] at h
  exact h

/-- 概要：零 loop 同値は通常の円の成分表示の逆元である。
方針：成分を円からの射で代表し、収縮による代表の計算を適用する。
規約：この逆元を既存の係数同型との比較から消さない。
使われ方：Goerss–Jardine I §8、VIII §1。零次数の標準比較の向き。 -/
theorem loopZeroHomotopyEquiv_eq_inv_component (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint) :
    loopZeroHomotopyEquiv Y a =
      (SphereSimplex.componentEquiv Y 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero a))⁻¹ := by
  obtain ⟨v, hv⟩ := π₀.mk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero a)
  obtain ⟨f, rfl⟩ := (PointedMapping.familyVertexEquiv PointedSimplicialSet.circle Y).surjective v
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 ((PtSimplex.equiv₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint).symm
        (PointedMapping.familyVertex f))) = π₀.mk (PointedMapping.familyVertex f) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk _) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_mk, Equiv.apply_symm_apply]
  have ha : a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 ((PtSimplex.equiv₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint).symm
      (PointedMapping.familyVertex f)) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.injective
    exact hv.symm.trans hp.symm
  have hc : SphereSimplex.componentEquiv Y 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv Y 1 f) := by
    change SphereSimplex.componentClass Y 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero a) = _
    rw [← hv]
    exact SphereSimplex.componentClass_familyVertex Y 0 f
  rw [hc, ha]
  exact loopZeroHomotopyEquiv_familyVertex Y f

end
end SerrePositivity.KST.Spectra
