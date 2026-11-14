module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Pullbacks.SphericalFiberRelation
public import SerrePositivity.KST.Spectra.LoopHomotopyGroups

/-!
概要：path の球面的境界から得る loop の交代和と、終点単体の符号の比較。
方針：相対交代境界を path fibration に適用し、既存の loop 同型の定義で連結射を消す。
規約：path と連結射の向きを変更しない。境界の面の次数は二以上。
使われ方：Goerss–Jardine I §8、VIII §1。loop とセルの向きの比較の入力。
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

namespace SphericalBoundary

/-- 概要：球面的な面の交代和は基点を保つ射の群準同型と可換。
方針：有限和と整数倍を準同型で移し、代表単体の像を計算する。
規約：面の実際の次数は n+2。
使われ方：Goerss–Jardine I §7。相対交代境界を同型で移す。 -/
lemma alternatingClass_map {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (φ : X ⟶ Y) (hφ : φ.app _ x = y) {n : ℕ}
    (a : Fin (n + 4) → X.PtSimplex (n + 2) x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n + 1) φ hφ).toAdditive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex φ hφ (a j)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass, map_sum, map_zsmul, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass,
    MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]

end SphericalBoundary

/-- 概要：既存の loop 群同型の逆向きは path の連結準同型そのもの。
方針：定義の fiber 同型、連結同型の逆、基点移送を順に消す。
規約：標的の基点は標準基点へ移す。群の添字 r は実次数 r+1。
使われ方：Goerss–Jardine I §7。path 境界を loop の係数表示へ移す。 -/
lemma connecting_loopPositiveHomotopyEquiv (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right r (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom (pathEndpoint Y).right (basedPathSpace Y).basepoint r
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl Y.right)
          (pathEndpoint_basepoint Y)).symm (loopPositiveHomotopyEquiv Y r a)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r (loopBasedPathFiberIso Y)
        (loopBasedPathFiberIso_basepoint Y) a := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHomEquivOfTotalSubsingleton (pathEndpoint Y).right
    (basedPathSpace Y).basepoint r)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl Y.right)
        (pathEndpoint_basepoint Y)).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl Y.right)
          (pathEndpoint_basepoint Y))
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHomEquivOfTotalSubsingleton (pathEndpoint Y).right
            (basedPathSpace Y).basepoint r).symm _))) = _
  rw [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  rfl

namespace SphericalPathBoundary

variable (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] {n : ℕ}
    (s : Y.right.PtSimplex (n + 3)
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint))
    (a : Fin (n + 4) → (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right.PtSimplex (n + 2) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (T : (Δ[n + 3] : SSet.{u}) ⟶ (basedPathSpace Y).right)
    (hT : T ≫ (pathEndpoint Y).right = s.map)
    (hface : ∀ j, stdSimplex.δ j ≫ T = (a j).map ≫
      (loopBasedPathFiberIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Y).right
        ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint))

include T hT hface

/-- 概要：path の境界に現れる loop の交代和は、終点単体の loop 類と符号付きで一致。
方針：相対球面的境界の等式を fiber 同型の単射性で loop の群へ戻す。
規約：符号は最後の面の添字 n+3。path の向きを反転しない。
使われ方：Goerss–Jardine I §8。loop の成分代表と幾何的境界の比較。 -/
theorem alternatingClass :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass a = (-1 : ℤ) ^ (n + 3) •
      Additive.ofMul ((loopPositiveHomotopyEquiv Y (n + 1)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 2) (Iso.refl Y.right)
          (pathEndpoint_basepoint Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s))) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (loopBasedPathFiberIso Y)
    (loopBasedPathFiberIso_basepoint Y)
  let L : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift (pathEndpoint Y).right (basedPathSpace Y).basepoint s
      (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (loopBasedPathFiberIso Y).hom
        (loopBasedPathFiberIso_basepoint Y) (a j)) :=
    { map := T
      map_comp := hT
      face_eq j := hface j }
  have h := L.alternatingClass_connecting
  have hc := connecting_loopPositiveHomotopyEquiv Y (n + 1)
    ((loopPositiveHomotopyEquiv Y (n + 1)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 2) (Iso.refl Y.right)
        (pathEndpoint_basepoint Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)))
  rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] at hc
  rw [hc] at h
  apply (MulEquiv.toAdditive e).injective
  rw [map_zsmul]
  have hm := SphericalBoundary.alternatingClass_map (loopBasedPathFiberIso Y).hom
    (loopBasedPathFiberIso_basepoint Y) a
  exact hm.trans h

/-- 概要：path の各境界 loop を元の高次群へ戻すと、交代和は終点単体の類。
方針：既存 loop 群同型を前の等式の有限和と整数倍へ適用する。
規約：終点単体には標準基点への移送のみを施す。符号は (-1)^(n+3)。
使われ方：Goerss–Jardine I §8、VIII §1。セルの微分と係数表示の符号の検査。 -/
theorem alternating_loopPositive :
    (∑ j, (-1 : ℤ) ^ j.val • Additive.ofMul
      (loopPositiveHomotopyEquiv Y (n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a j)))) =
      (-1 : ℤ) ^ (n + 3) • Additive.ofMul
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 2) (Iso.refl Y.right)
          (pathEndpoint_basepoint Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) := by
  have h := congrArg (MulEquiv.toAdditive (loopPositiveHomotopyEquiv Y (n + 1)))
    (alternatingClass Y s a T hT hface)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass,
    map_sum, map_zsmul, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    MulEquiv.apply_symm_apply] using h

end SphericalPathBoundary
end
end SerrePositivity.KST.Spectra
