module

public import SerrePositivity.KST.Spectra.LoopBoundaryRepresentatives

/-!
概要：共通持ち上げの逆元公式を標準の点つき連結準同型の代表へ移す。
方針：底の代表の基点だけを path の基点へ移し、最後の面の loop の代表を固定する。
規約：連結射と loop 同型は既存のものを使う。
使われ方：Goerss–Jardine I §8。全正次数の標準準同型の反可換式。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.LoopConnectingComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) {n : ℕ}
  (s : B.right.PtSimplex (n + 2) (p.right.app _ E.basepoint))

/-- 底の代表の射を保ち、path の連結射に必要な基点へ移す。 -/
def pathBaseSimplex : B.right.PtSimplex (n + 2)
    ((pathEndpoint B).right.app _ (basedPathSpace B).basepoint) :=
  SimplexBasepoint.rebase ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p).trans
    (pathEndpoint_basepoint B).symm) s

variable (M : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pathEndpoint B).right (basedPathSpace B).basepoint
  (pathBaseSimplex p s))

/-- 底の path の最後の面を、loop の連結射の像の基点で表示する。 -/
def sourceLoop : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right.PtSimplex (n + 1)
    ((PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right.app _
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint) :=
  SimplexBasepoint.rebase
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p)).symm
    (_root_.SerrePositivity.KST.Spectra.BoundaryLift.loopSimplex M)

/-- loop の標準基点へ戻すと、path の最後の面の元の代表の類になる。 -/
lemma sourceLoop_class [KanComplex B.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n) (Iso.refl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
          (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (sourceLoop p s M)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.KST.Spectra.BoundaryLift.loopSimplex M) := by
  rw [SimplexBasepoint.group_mk]
  congr 1

/-- 概要：標準 loop 同型で源の loop を戻すと、元の底の代表の標準基点での類。
方針：path の最後の面の代表公式と、恒等射の基点移送を計算する。
規約：底の実際の次数は n+2。
使われ方：Goerss–Jardine I §8。反可換式の入力の同定。 -/
lemma sourceLoop_positive [KanComplex B.right] :
    loopPositiveHomotopyEquiv B (n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n) (Iso.refl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
          (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (sourceLoop p s M))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl B.right)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) := by
  rw [sourceLoop_class, BoundaryLift.loopPositive_loopSimplex,
    SimplexBasepoint.group_mk, SimplexBasepoint.group_mk]
  congr 1

/-- path に含めた源の loop の単体は、元の path 充填の最後の面そのもの。 -/
lemma sourceLoop_toPath : (pathSimplex p (v := sourceLoop p s M)).map =
    stdSimplex.δ (Fin.last (n + 2)) ≫ M.map := (_root_.SerrePositivity.KST.Spectra.BoundaryLift.loopSimplex_toPath M)

/-- 概要：標準の二つの連結射の充填から共通の path の単体を構成する。
方針：二つの充填の共通持ち上げの最後の面を取り、fiber 内の終点が元の境界に等しいと示す。
規約：単体の厳密な一致。ホモトピー群の単射性は使わない。
使われ方：Goerss–Jardine I §8。共通持ち上げの逆元公式への代入。 -/
theorem exists_standard_common [Fibration p.right] (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p.right E.basepoint s) :
    ∃ (U : (basedPathSpace E).right.PtSimplex (n + 1) (basedPathSpace E).basepoint)
      (hU : U.map ≫ (basedPathMap p).right = (pathSimplex p (v := sourceLoop p s M)).map),
      sourceFiberSimplex p U hU = L.boundary := by
  obtain ⟨U, hU, hend⟩ := RelativePath.common_boundary_simplex p (n + 1) L.map M.map
    (by rw [M.map_comp, L.map_comp]; rfl) L.face_eq M.face_eq
  have hp : U.map ≫ (basedPathMap p).right = (pathSimplex p (v := sourceLoop p s M)).map :=
    hU.trans (sourceLoop_toPath p s M).symm
  refine ⟨U, hp, ?_⟩
  ext : 1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p.right (p.right.app _ E.basepoint)
  simp only [sourceFiberSimplex, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex]
  rw [L.boundary_ι]
  exact hend

/-- 概要：標準の連結準同型は、path の最後の面から得る loop の代表で反可換。
方針：両連結射を任意の充填の境界で計算し、共通の path の逆元公式を使う。
規約：標準の fiber 基点と既存 loop–fiber 同型を保持する。
使われ方：Goerss–Jardine I §8。商の任意の入力に移す前の代表での式。 -/
theorem pointedConnecting_loop_representative [Fibration p.right]
    [KanComplex E.right] [KanComplex B.right]
    (t : B.right.PtSimplex (n + 3) (p.right.app _ E.basepoint))
    (N : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pathEndpoint B).right (basedPathSpace B).basepoint (pathBaseSimplex p t))
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p.right E.basepoint t)
    (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint (sourceLoop p t N)) :
    loopPositiveHomotopyEquiv (pointedFiber p) n
      (pointedGroupMap n (loopPointedFiberIso p).inv
        (pointedConnectingHom (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p) n
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right)
            (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
              (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (sourceLoop p t N))))) =
      (pointedConnectingHom p (n + 1)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 2) (Iso.refl B.right)
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t)))⁻¹ := by
  have : Fibration (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right := by
    infer_instance
  apply (pointedFiberGroupEquiv p (n + 1)).injective
  rw [map_inv, pointedConnectingHom_boundaryLift p (n + 1) L,
    BoundaryLift.pointedFiberGroupEquiv_mk, pointedConnectingHom_boundaryLift _ n V]
  change pointedFiberGroupEquiv p (n + 1)
    (loopPositiveHomotopyEquiv (pointedFiber p) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (boundaryLoop p V))) = _
  obtain ⟨U, hU, hend⟩ := exists_standard_common p t N L
  have he := boundaryLoop_inverse_common p V U hU
  rw [hend] at he
  exact he

end
end SerrePositivity.KST.Spectra.LoopConnectingComparison
