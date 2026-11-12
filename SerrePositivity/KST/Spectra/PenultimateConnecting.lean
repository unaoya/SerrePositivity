module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberNormalization
public import SerrePositivity.KST.Spectra.SphericalPathBoundary

/-!
概要：最後から二番目の面だけが非定数の持ち上げの連結射を計算する。
方針：終端の相対ホーンで境界を逆元の最後の面へ正規化する。
規約：面次数一も含む。可換性や交代和を使わず群の逆元として比較する。
使われ方：Goerss–Jardine I §8。loop と連結射の交換の全正次数の符号。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：最後から二番目に一面だけが残る持ち上げの連結射は、その面の類の逆元。
方針：逆元と単位の積を使って終端の二面を正規化し、最後の面の代表を計算する。
規約：任意の正次数。n=0 では fiber の基本群を使う。
使われ方：Goerss–Jardine I §8。隣接面の向きの差を群の値で比較する。 -/
theorem connectingHom_penultimate {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p] [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ)
    (s : B.PtSimplex (n + 2) (p.app _ e))
    (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e))
    (T : (Δ[n + 2] : SSet.{u}) ⟶ E) (hT : T ≫ p = s.map)
    (hface : ∀ j, stdSimplex.δ j ≫ T =
      if j.val = n + 1 then a.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) else SSet.const e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p e n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a)⁻¹ := by
  let b (j : Fin (n + 3)) := if j.val = n + 1 then a else RelativeMorphism.const
  let L : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift p e s b :=
    { map := T
      map_comp := hT
      face_eq j := by
        rw [hface]
        dsimp only [b]
        split_ifs <;> simp only [RelativeMorphism.const_map, const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point] }
  obtain ⟨ia, ⟨hi⟩⟩ := PtSimplex.MulStruct.exists_left_inverse a (Fin.last n)
  have hi' : PtSimplex.MulStruct ia (b (Fin.last (n + 1)).castSucc) .const (Fin.last n) := by
    simpa only [b, Fin.val_castSucc, Fin.val_last, ite_true] using hi
  have hc : PtSimplex.MulStruct ia (b (Fin.last (n + 1)).succ) ia (Fin.last n) := by
    simpa only [b, Fin.val_succ, Fin.val_last, show ¬n + 1 + 1 = n + 1 by omega,
      ite_false] using PtSimplex.MulStruct.mulOne ia (Fin.last n)
  have hlower : ∀ j, j.val < n + 1 → b j = .const := by
    intro j hj
    simp only [b, ite_eq_right (show j.val ≠ n + 1 by omega)]
  have hboundary := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.terminalLift_boundary hi' hc L hlower
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.terminalLift hi' hc L hlower), hboundary]
  exact eq_inv_of_mul_eq_one_left (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq hi)

/-- 概要：path の最後から二番目の loop 面を高次群へ戻すと、終点単体の逆元になる。
方針：相対終端の逆元公式と、既存 loop 同型の連結同型による定義を照合する。
規約：全正次数、標準基点への移送を保持する。
使われ方：Goerss–Jardine I §8。loop と連結射の交換の負符号。 -/
theorem loopPositive_penultimate (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n : ℕ) (s : Y.right.PtSimplex (n + 2)
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint))
    (a : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right.PtSimplex (n + 1) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (T : (Δ[n + 2] : SSet.{u}) ⟶ (basedPathSpace Y).right)
    (hT : T ≫ (pathEndpoint Y).right = s.map)
    (hface : ∀ j, stdSimplex.δ j ≫ T = if j.val = n + 1 then
      a.map ≫ (loopBasedPathFiberIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Y).right
        ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint)
      else SSet.const (basedPathSpace Y).basepoint) :
    loopPositiveHomotopyEquiv Y n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl Y.right)
        (pathEndpoint_basepoint Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s))⁻¹ := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom (pathEndpoint Y).right (basedPathSpace Y).basepoint n
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (loopBasedPathFiberIso Y)
    (loopBasedPathFiberIso_basepoint Y)
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl Y.right) (pathEndpoint_basepoint Y)
  have hc := connectingHom_penultimate (pathEndpoint Y).right (basedPathSpace Y).basepoint n s
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (loopBasedPathFiberIso Y).hom (loopBasedPathFiberIso_basepoint Y) a) T hT hface
  have hc' : e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a) = (c (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s))⁻¹ := by
    have hi := congrArg Inv.inv hc
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (loopBasedPathFiberIso Y).hom
      (loopBasedPathFiberIso_basepoint Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
    simpa only [inv_inv, c] using hi.symm
  have hr : b.symm (loopPositiveHomotopyEquiv Y n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)⁻¹ := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHomEquivOfTotalSubsingleton (pathEndpoint Y).right
      (basedPathSpace Y).basepoint n).injective
    change c _ = c _
    rw [show c (b.symm (loopPositiveHomotopyEquiv Y n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a))) =
      e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a) from connecting_loopPositiveHomotopyEquiv Y n _, hc', map_inv]
  have hr' := congrArg b hr
  simpa only [MulEquiv.apply_symm_apply, map_inv] using hr'

end
end SerrePositivity.KST.Spectra
