module

public import SerrePositivity.KST.Spectra.ReverseBoundaryEdge
public import SerrePositivity.KST.Spectra.LoopZeroHomotopy
public import SerrePositivity.KST.Spectra.MappingFiberPaths

/-!
概要：零 loop 成分について、逆向きの path の終点の基本群の値を計算する。
方針：底の逆元の三角形を相対充填して正向きの連結射に直し、既存 loop 零次数同値を使う。
規約：fiber の π₀ は集合として扱い、群の逆元は終点空間の基本群で取る。
使われ方：Goerss–Jardine I §8。連結射と零 loop 成分の交換の基本段。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：零 loop 同値を path の連結写像へ戻すと、fiber 同型による元の成分になる。
方針：定義の二つの同値と基点移送を順に打ち消す。
規約：成分集合に群演算を置かない。
使われ方：Goerss–Jardine I §7–8。零 loop の代表計算。 -/
lemma connecting_loopZeroHomotopyEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (a : KanHomotopy (loopSpace Y).right 0 (loopSpace Y).basepoint) :
    connecting (pathEndpoint Y).right (basedPathSpace Y).basepoint 0
        ((KanHomotopyGroup.equivOfIso 0 (Iso.refl Y.right) (pathEndpoint_basepoint Y)).symm
          (loopZeroHomotopyEquiv Y a)) =
      KanHomotopy.equivOfIso 0 (loopBasedPathFiberIso Y) (loopBasedPathFiberIso_basepoint Y) a := by
  change (connectingZeroEquiv (pathEndpoint Y).right (basedPathSpace Y).basepoint
    (basedPathSpace_terminal_rlp Y))
      ((KanHomotopyGroup.equivOfIso 0 (Iso.refl Y.right) (pathEndpoint_basepoint Y)).symm
        ((KanHomotopyGroup.equivOfIso 0 (Iso.refl Y.right) (pathEndpoint_basepoint Y))
          ((connectingZeroEquiv (pathEndpoint Y).right (basedPathSpace Y).basepoint
            (basedPathSpace_terminal_rlp Y)).symm _))) = _
  rw [MulEquiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- 概要：零 loop の path 面が終点側だけに現れる族は、終点の基本群の逆元を表す。
方針：逆元の辺を正向きの BoundaryLift として構成し、連結零次数同値の単射性で比較する。
規約：底の群は基本群。fiber の成分は最後まで集合のまま扱う。
使われ方：Goerss–Jardine I §8。零 loop 成分の反可換性の向き。 -/
theorem loopZero_penultimate (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (s : Y.right.PtSimplex 1 ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint))
    (a : (loopSpace Y).right.PtSimplex 0 (loopSpace Y).basepoint)
    (T : (Δ[1] : SSet.{u}) ⟶ (basedPathSpace Y).right)
    (hT : T ≫ (pathEndpoint Y).right = s.map)
    (h₀ : stdSimplex.δ (0 : Fin 2) ≫ T = a.map ≫ (PointedMapping.loopToPath Y).right)
    (h₁ : stdSimplex.δ (1 : Fin 2) ≫ T = SSet.const (basedPathSpace Y).basepoint) :
    loopZeroHomotopyEquiv Y (KanHomotopy.mk 0 a) =
      (KanHomotopyGroup.equivOfIso 0 (Iso.refl Y.right) (pathEndpoint_basepoint Y)
        (KanHomotopyGroup.mk s))⁻¹ := by
  obtain ⟨t, ⟨m⟩⟩ := PtSimplex.MulStruct.exists_left_inverse s (0 : Fin 1)
  let af := mapSimplex (loopBasedPathFiberIso Y).hom (loopBasedPathFiberIso_basepoint Y) a
  have ha : stdSimplex.δ (0 : Fin 2) ≫ T = af.map ≫ fiberι (pathEndpoint Y).right
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) := by
    rw [h₀]
    change a.map ≫ (PointedMapping.loopToPath Y).right =
      (a.map ≫ (loopBasedPathFiberIso Y).hom) ≫ _
    rw [Category.assoc, PointedMapping.loopToPath_fiber]
  obtain ⟨R, hR⟩ := exists_reverse_boundary_edge (pathEndpoint Y).right
    (basedPathSpace Y).basepoint af T hT ha h₁ m
  let b := KanHomotopyGroup.equivOfIso 0 (Iso.refl Y.right) (pathEndpoint_basepoint Y)
  have hc : connecting (pathEndpoint Y).right (basedPathSpace Y).basepoint 0
      (KanHomotopyGroup.mk t) =
      KanHomotopy.equivOfIso 0 (loopBasedPathFiberIso Y)
        (loopBasedPathFiberIso_basepoint Y) (KanHomotopy.mk 0 a) := by
    rw [connecting_eq _ _ R, hR]
    rfl
  have he : loopZeroHomotopyEquiv Y (KanHomotopy.mk 0 a) = b (KanHomotopyGroup.mk t) := by
    apply b.symm.injective
    apply (connectingZeroEquiv (pathEndpoint Y).right (basedPathSpace Y).basepoint
      (basedPathSpace_terminal_rlp Y)).injective
    change connecting (pathEndpoint Y).right (basedPathSpace Y).basepoint 0 _ = _
    rw [MulEquiv.symm_apply_apply, connecting_loopZeroHomotopyEquiv]
    exact hc.symm
  have hi : KanHomotopyGroup.mk t = (KanHomotopyGroup.mk s)⁻¹ :=
    eq_inv_of_mul_eq_one_left (KanHomotopyGroup.mul_eq m)
  rw [he, hi, map_inv]

end
end SerrePositivity.KST.Spectra
