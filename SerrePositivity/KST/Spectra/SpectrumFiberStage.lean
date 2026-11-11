module

public import SerrePositivity.KST.Spectra.FiberOmegaSpectrum
public import SerrePositivity.KST.Spectra.StageComparisonNaturality

/-!
概要：整数次数の群と、fiber の長完全列を計算する正次数の段の比較。
方針：任意段の自然同型、置換の段の π_* 同型、基点の移送を合成する。
規約：各段の fibration 仮定は Π 型のインスタンスとして受け取る。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。整数次数の長完全列。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：標的の指定基点から像の基点へ戻すと元の射の像の基点での誘導写像となる。
方針：基点移送の群同型の単射性と合成の関手性を使う。
規約：同型は恒等射から作る。
使われ方：Goerss–Jardine I §7。点つき射と fibration の完全列の基点の一致。 -/
theorem KanHomotopyGroup.map_basepoint_transport {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) {e : E _⦋0⦌} {b : B _⦋0⦌}
    (hb : p.app _ e = b) (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup E n e) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (Iso.refl B) hb).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p hb a) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl a := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (Iso.refl B) hb
  apply i.injective
  rw [MulEquiv.apply_symm_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p hb a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 B) hb (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl a)
  have hc := DFunLike.congr_fun
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n) (x := e) (y := p.app _ e) (z := b) p rfl (𝟙 B) hb hb) a
  exact (DFunLike.congr_fun
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_congr (x := e) (y := b) n (Category.comp_id p) hb hb) a).symm.trans hc

namespace OmegaSpectrum

/-- 概要：整数次数の群を正次数の指定段で計算する群同型。
方針：任意段の比較同型に次数の等式による移送を合成する。
規約：実際の計算次数は n+1。
使われ方：BF 1978 §2、HA §1.4.2。段の長完全列への接続。 -/
def positiveStageEquiv (X : OmegaSpectrum.{u}) (j : ℤ) (k n : ℕ)
    (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1) :
    homotopyGroup X j ≃* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X.level k).space.right n (X.level k).space.basepoint :=
  (homotopyGroupEquivAt X j k hk).trans (levelHomotopyCongr X rfl hd)

/-- 概要：正次数の段による整数次数群の表示は自然。
方針：任意段の自然性と次数の等式の自然性を合成する。
規約：同じ k,n を両スペクトルで使う。
使われ方：BF 1978 §2、HA §1.4.2。完全列の全空間と底の比較。 -/
theorem positiveStageEquiv_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (k n : ℕ) (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1)
    (a : homotopyGroup X j) :
    positiveStageEquiv Y j k n hk hd (homotopyMap f j a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (f.app k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
        (positiveStageEquiv X j k n hk hd a) := by
  simp only [positiveStageEquiv, MulEquiv.trans_apply]
  rw [homotopyGroupEquivAt_natural]
  exact levelHomotopyCongr_natural f rfl hd _

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) [hp : ∀ k, Fibration (p.app k).right]

/-- 概要：fiber の段の比較射は実際の fiberPoint へ基点を送る。
方針：点つき基点保存と ofVertex の基点の式を合成する。
規約：fibration の完全列の基点と同じ表示。
使われ方：Goerss–Jardine I §7。fiber の段の群同型。 -/
theorem fiberLevelProjection_basepoint (k : ℕ) :
    (fiberLevelProjection p hp k).right.app _ ((fiber p hp).level k).space.basepoint =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint (p.app k).right (X.level k).space.basepoint :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (fiberLevelProjection p hp k)).trans
    (PointedSimplicialSet.basepoint_ofVertex _ _)

/-- 概要：置換した fiber の段の群と実際の fiber の正次数の群の同型。
方針：段の比較射の全基点 π_* 同型と基点保存を使う。
規約：実際の次数は n+1。
使われ方：Goerss–Jardine I §7、BF 1978 §2。置換を挟んだ完全列の計算。 -/
def fiberProjectionGroupEquiv (k n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((fiber p hp).level k).space.right n ((fiber p hp).level k).space.basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (p.app k).right
        ((p.app k).right.app _ (X.level k).space.basepoint)) n
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint (p.app k).right (X.level k).space.basepoint) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n (fiberLevelProjection p hp k).right
    (fiberLevelProjection_piIsomorphism p hp k) (fiberLevelProjection_basepoint p k)

/-- 概要：fiber の段の群同型の順写像は元の段の比較射の誘導準同型。
方針：全単射から作った群同型の計算式を使う。
規約：実際の fiberPoint を標的の基点にする。
使われ方：Goerss–Jardine I §7。fiber 包含との可換性。 -/
@[simp]
theorem fiberProjectionGroupEquiv_apply (k n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((fiber p hp).level k).space.right n
      ((fiber p hp).level k).space.basepoint) :
    fiberProjectionGroupEquiv p k n a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
      (fiberLevelProjection p hp k).right (fiberLevelProjection_basepoint p k) a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply _ _ _ _ a

/-- 概要：整数次数の fiber の群を実際の段の fiber の正次数の群で計算する。
方針：正次数の段の表示と置換の比較射の群同型を合成する。
規約：実際の次数は n+1。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の連結準同型の標的。 -/
def fiberPositiveStageEquiv (j : ℤ) (k n : ℕ) (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1) :
    homotopyGroup (fiber p hp) j ≃* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (p.app k).right
      ((p.app k).right.app _ (X.level k).space.basepoint)) n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint (p.app k).right (X.level k).space.basepoint) :=
  (positiveStageEquiv (fiber p hp) j k n hk hd).trans (fiberProjectionGroupEquiv p k n)

/-- 概要：整数次数の fiber 包含は段の実際の fiber 包含に対応する。
方針：スペクトルの射に関する自然性と、段の比較射との合成の計算を使う。
規約：指定した正次数の段で計算する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。完全列の fiber の位置。 -/
theorem fiberPositiveStageEquiv_inclusion (j : ℤ) (k n : ℕ)
    (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1) (a : homotopyGroup (fiber p hp) j) :
    positiveStageEquiv X j k n hk hd (homotopyMap (fiberInclusion p hp) j a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (p.app k).right
        ((p.app k).right.app _ (X.level k).space.basepoint))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point (p.app k).right (X.level k).space.basepoint)
          (fiberPositiveStageEquiv p j k n hk hd a) := by
  rw [positiveStageEquiv_natural]
  simp only [fiberPositiveStageEquiv, MulEquiv.trans_apply, fiberProjectionGroupEquiv_apply]
  exact DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (fiberLevelProjection p hp k).right
    (fiberLevelProjection_basepoint p k) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (p.app k).right _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point (p.app k).right (X.level k).space.basepoint)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint ((fiberInclusion p hp).app k))) _

omit hp in
/-- 概要：整数次数の元の射は、基点を像へ戻すと段の fibration の射に対応する。
方針：正次数の段の自然性と恒等射による基点移送の計算を使う。
規約：標的の基点は p が全空間の基点に取る値。
使われ方：Goerss–Jardine I §7、BF 1978 §2。完全列の全空間の位置。 -/
theorem positiveStageEquiv_projection (j : ℤ) (k n : ℕ)
    (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1) (a : homotopyGroup X j) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (Iso.refl (Y.level k).space.right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p.app k))).symm
        (positiveStageEquiv Y j k n hk hd (homotopyMap p j a)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (p.app k).right rfl (positiveStageEquiv X j k n hk hd a) := by
  rw [positiveStageEquiv_natural]
  exact KanHomotopyGroup.map_basepoint_transport (p.app k).right _ n _

end OmegaSpectrum

end

end SerrePositivity.KST.Spectra
