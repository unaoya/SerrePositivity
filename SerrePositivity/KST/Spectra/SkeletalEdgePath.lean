module

public import SerrePositivity.KST.Spectra.SkeletalEdgeCochain
public import SerrePositivity.KST.Spectra.PathTriangleBoundary
public import SerrePositivity.KST.Spectra.SkeletalCellBoundaryRestriction
public import SerrePositivity.KST.Spectra.LoopBoundaryRepresentatives

/-!
概要：次数一の loop 値の骨格射を path 空間へ延長し、その終点の係数を計算する。
方針：可縮な path 空間の RLP で一段延長し、各二単体に相対三角形の公式を適用する。
規約：延長の選択は任意。向きは標準の区間のまま。
使われ方：Goerss–Jardine VIII §1。次数一の正規化微分の幾何的計算。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalEdgePath

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open UnbasedPointedMapping SkeletalCellAttachment

variable (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
  (f : (K.skeleton 2 : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)

/-- 次数一の loop 族の path 表示は、二単体の骨格へ必ず延長できる。 -/
theorem exists_extension [KanComplex Y.right] :
    ∃ H : (K.skeleton 3 : SSet.{u}) ⟶ (basedPathSpace Y).right,
      skeletalInclusion K 1 ≫ H = f ≫ (PointedMapping.loopToPath Y).right := by
  let i := skeletalInclusion K 1
  let : HasLiftingProperty i (terminal.from (basedPathSpace Y).right) :=
    basedPathSpace_terminal_rlp Y i inferInstance
  let sq : CommSq (f ≫ (PointedMapping.loopToPath Y).right) i
      (terminal.from (basedPathSpace Y).right) (terminal.from (K.skeleton 3 : SSet.{u})) :=
    ⟨Subsingleton.elim _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

variable (H : (K.skeleton 3 : SSet.{u}) ⟶ (basedPathSpace Y).right)
  (hH : skeletalInclusion K 1 ≫ H = f ≫ (PointedMapping.loopToPath Y).right)

include hH in
/-- 延長の終点は元の辺の骨格で定数。 -/
lemma endpoint_lower : skeletalInclusion K 1 ≫ (H ≫ (pathEndpoint Y).right) =
    SSet.const Y.basepoint := by
  rw [← Category.assoc, hH, Category.assoc, PointedMapping.loopToPath_endpoint, comp_const]

/-- 終点の各二単体を境界定数単体として読む。 -/
def endpointSimplex (s : K _⦋2⦌) : Y.right.PtSimplex 2 Y.basepoint :=
  SkeletalMapSimplex.simplex K Y 1 (H ≫ (pathEndpoint Y).right) (endpoint_lower K Y f H hH) s

/-- 各二単体での path 延長。 -/
def cellPath (s : K _⦋2⦌) : (Δ[2] : SSet.{u}) ⟶ (basedPathSpace Y).right :=
  SSet.yonedaEquiv.symm (⟨s, K.mem_skeleton _⟩ : (K.skeleton 3 : SSet.{u}) _⦋2⦌) ≫ H

/-- 各セルの終点は指定した二単体。 -/
lemma cellPath_endpoint (s : K _⦋2⦌) :
    cellPath K Y H s ≫ (pathEndpoint Y).right = (endpointSimplex K Y f H hH s).map := rfl

include hH in
/-- セルの各辺の path は元の loop の辺の path 表示。 -/
lemma cellPath_face (hf : skeletalInclusion K 0 ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (s : K _⦋2⦌) (j : Fin 3) :
    stdSimplex.δ j ≫ cellPath K Y H s =
      (SkeletalMapSimplex.simplex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 f hf (K.δ j s)).map ≫
        (PointedMapping.loopToPath Y).right := by
  have he : stdSimplex.δ j ≫ SSet.yonedaEquiv.symm
      (⟨s, K.mem_skeleton _⟩ : (K.skeleton 3 : SSet.{u}) _⦋2⦌) =
      SSet.yonedaEquiv.symm
        (⟨K.δ j s, K.mem_skeleton _⟩ : (K.skeleton 2 : SSet.{u}) _⦋1⦌) ≫
          skeletalInclusion K 1 := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, yonedaEquiv_symm_comp]
    rfl
  change stdSimplex.δ j ≫ (SSet.yonedaEquiv.symm _ ≫ H) = _
  rw [← Category.assoc, he, Category.assoc, hH]
  rfl

/-- 延長の終点が定める実際の fiber 頂点。 -/
def endpointFiberVertex : (stageFiber K Y 1).right _⦋0⦌ :=
  skeletalFiberVertex K Y 1 (H ≫ (pathEndpoint Y).right) (endpoint_lower K Y f H hH)

/-- 終点の fiber 成分の係数は、指定した二単体の類。 -/
lemma endpointFiberVertex_coefficient [KanComplex Y.right] (s : K.nonDegenerate 2) :
    stageFiberComponentEquiv K Y 1 (π₀.mk (endpointFiberVertex K Y f H hH)) s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (endpointSimplex K Y f H hH s.val) :=
  SkeletalMapSimplex.fiberVertex_coefficient K Y 1 _ _ s

/-- 次数一の正規化微分を loop 群同型で送ると、path 延長の終点の類になる。 -/
theorem normalizedDifferential_endpoint [KanComplex Y.right]
    (hf : skeletalInclusion K 0 ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (s : K.nonDegenerate 2) :
    (loopPositiveHomotopyEquiv Y 0).toAdditive
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint))) 1
        (SkeletalEdgeCochain.cochain K Y f hf) s) =
      Additive.ofMul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (endpointSimplex K Y f H hH s.val)) := by
  let b := SimplexBasepoint.rebase (pathEndpoint_basepoint Y).symm
    (endpointSimplex K Y f H hH s.val)
  let a := fun j : Fin 3 ↦ SkeletalMapSimplex.simplex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 f hf (K.δ j s.val)
  have hface : ∀ j, stdSimplex.δ j ≫ cellPath K Y H s.val =
      (a j).map ≫ (loopBasedPathFiberIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Y).right
        ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) := by
    intro j
    rw [PointedMapping.loopToPath_fiber]
    exact cellPath_face K Y f H hH hf s.val j
  have h := PathTriangleBoundary.alternating_loopPositive Y b a (cellPath K Y H s.val)
    (cellPath_endpoint K Y f H hH s.val) hface
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 1 (Iso.refl Y.right) (pathEndpoint_basepoint Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (endpointSimplex K Y f H hH s.val) := by
    rw [SimplexBasepoint.group_mk]
    congr 1
  rw [hb] at h
  rw [SkeletalEdgeCochain.differential]
  simpa only [map_sum, map_zsmul, MulEquiv.toAdditive_apply_apply, toMul_ofMul] using h

end
end SerrePositivity.KST.Spectra.SkeletalEdgePath
