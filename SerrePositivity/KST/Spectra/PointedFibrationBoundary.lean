module

public import SerrePositivity.KST.Spectra.PointedFiber
public import SerrePositivity.KST.Spectra.PointedGroupProduct
public import SerrePositivity.InfinityCategories.Kan.FibrationSequence
public import SerrePositivity.KST.Spectra.SpectrumFiberStage

/-!
概要：点つき Kan fibration の標準基点での連結準同型。
方針：L9b の像の基点での連結準同型を基点の等式による群同型で移す。
規約：正次数の群の添字 r は実際の r+1。
使われ方：Goerss–Jardine I §§7–8、VIII §1。骨格の塔の連結準同型。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) [Fibration p.right]
  [KanComplex E.right] [KanComplex B.right]

/-- 概要：点つき fiber の群を L9b の実際の fiberPoint で表示する。
方針：ofVertex の基点の等式を恒等射による群同型にする。
規約：基礎単体集合は同じ pullback。
使われ方：Goerss–Jardine I §7。点つき連結射の終域の比較。 -/
def pointedFiberGroupEquiv (r : ℕ) :
    KanHomotopyGroup (pointedFiber p).right r (pointedFiber p).basepoint ≃*
      KanHomotopyGroup (KanFiber p.right (p.right.app _ E.basepoint)) r
        (fiberPoint p.right E.basepoint) :=
  KanHomotopyGroup.equivOfIso r (Iso.refl (KanFiber p.right (p.right.app _ E.basepoint)))
    (PointedSimplicialSet.basepoint_ofVertex _ _)

/-- 概要：標準基点での点つき Kan fibration の連結準同型。
方針：像の基点へ移し、相対ホーンからの連結射を適用し、点つき fiber へ戻す。
規約：π_(r+2)(B) から π_(r+1)(fiber) への準同型。
使われ方：Goerss–Jardine I §§7–8、VIII §1。塔の微分の構成。 -/
def pointedConnectingHom (r : ℕ) :
    KanHomotopyGroup B.right (r + 1) B.basepoint →*
      KanHomotopyGroup (pointedFiber p).right r (pointedFiber p).basepoint :=
  (pointedFiberGroupEquiv p r).symm.toMonoidHom.comp
    ((connectingHom p.right E.basepoint r).comp
      (KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl B.right)
        (OmegaSpectrum.pointedMap_basepoint p)).symm.toMonoidHom)

lemma pointedConnectingHom_compute (r : ℕ)
    (a : KanHomotopyGroup B.right (r + 1) B.basepoint) :
    pointedFiberGroupEquiv p r (pointedConnectingHom p r a) =
      connectingHom p.right E.basepoint r
        ((KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl B.right)
          (OmegaSpectrum.pointedMap_basepoint p)).symm a) :=
  (pointedFiberGroupEquiv p r).apply_symm_apply _

omit [KanComplex B.right] in
lemma pointedFiberGroupEquiv_inclusion (r : ℕ)
    (a : KanHomotopyGroup (pointedFiber p).right r (pointedFiber p).basepoint) :
    pointedGroupMap r (pointedFiberι p) a =
      KanHomotopyGroup.map (fiberι p.right (p.right.app _ E.basepoint))
        (fiberι_point p.right E.basepoint) (pointedFiberGroupEquiv p r a) := by
  change KanHomotopyGroup.map (fiberι p.right (p.right.app _ E.basepoint)) _ a =
    KanHomotopyGroup.map (fiberι p.right (p.right.app _ E.basepoint)) _
      (KanHomotopyGroup.map (𝟙 _) _ a)
  erw [← DFunLike.congr_fun (KanHomotopyGroup.map_comp _ _ _ _ _) a]
  rfl

/-- 概要：点つき連結準同型と fiber 包含の誘導準同型の合成は自明。
方針：基点の群同型で L9b の零合成へ帰着する。
規約：乗法記法で自明な値は単位。
使われ方：Goerss–Jardine VIII §1。骨格の塔の微分の二乗の零性。 -/
@[simp]
theorem pointedConnectingHom_inclusion (r : ℕ)
    (a : KanHomotopyGroup B.right (r + 1) B.basepoint) :
    pointedGroupMap r (pointedFiberι p) (pointedConnectingHom p r a) = 1 := by
  rw [pointedFiberGroupEquiv_inclusion, pointedConnectingHom_compute]
  exact fiber_map_connecting p.right E.basepoint (r + 1) _

/-- 概要：元の点つき射の誘導像は連結準同型で自明。
方針：基点移送の計算で L9b の全空間からの像に対する零合成を使う。
規約：全空間の次数は r+2。
使われ方：Goerss–Jardine I §8、VIII §1。塔の微分の構造式。 -/
@[simp]
theorem pointedConnectingHom_projection (r : ℕ)
    (a : KanHomotopyGroup E.right (r + 1) E.basepoint) :
    pointedConnectingHom p r (pointedGroupMap (r + 1) p a) = 1 := by
  apply (pointedFiberGroupEquiv p r).injective
  rw [pointedConnectingHom_compute, map_one]
  change connectingHom p.right E.basepoint r
    ((KanHomotopyGroup.equivOfIso (r + 1) (Iso.refl B.right)
      (OmegaSpectrum.pointedMap_basepoint p)).symm
        (KanHomotopyGroup.map p.right (OmegaSpectrum.pointedMap_basepoint p) a)) = 1
  rw [KanHomotopyGroup.map_basepoint_transport]
  exact connecting_map p.right E.basepoint (r + 1) a

end

end SerrePositivity.KST.Spectra
