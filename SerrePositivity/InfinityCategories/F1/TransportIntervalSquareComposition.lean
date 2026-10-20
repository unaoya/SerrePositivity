module

public import SerrePositivity.InfinityCategories.F1.TransportIntervalSquare

/-!
概要：指定した同じ四角形に沿う二通りの対角輸送を、全パラメーターで比較する。
方針：最初の辺の普遍輸送を四角形全体へ持ち上げ、同じ終点を三つの辺で評価する。
規約：元の四辺を厳密に保ち、各頂点で独立な比較を選ばない。
使われ方：右 Hom 合成の四角形から、元の点評価と合成の両立を導く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ全パラメーターの四角形の二つの合成順序の対角輸送は、一つの関手同型を持つ。 -/
def TransportIntervalSquare.transportIso {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b c d : B _⦋0⦌}
    (s : TransportIntervalSquare P a b c d) (f : P ⟶ vertexFiber p a) :
    FunctorIso
      (diagonalFiberTransport p (diagonalFiberTransport p f s.bottom) s.right)
      (diagonalFiberTransport p (diagonalFiberTransport p f s.left) s.top) := by
  let T := parametrizedFiberTransportFamily p a b
  let j := lift f s.bottom
  let V := (Δ[1] ◁ j) ≫ T.prism
  have V₀ : prismEndpoint 0 P ≫ V = f ≫ vertexFiberι p a := by
    dsimp only [V]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.start,
      ← Category.assoc, ← Category.assoc]
    change (j ≫ fst _ _) ≫ (𝟙 _ ≫ vertexFiberι p a) = _
    rw [lift_fst, Category.id_comp]
  have V₁ : prismEndpoint 1 P ≫ V = diagonalFiberTransport p f s.bottom ≫ vertexFiberι p b := by
    dsimp only [V]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.finish]
    rfl
  have Vp : V ≫ p = intervalMappingUncurry s.bottom := by
    dsimp only [V]
    rw [Category.assoc, T.over_base, ← whiskerLeft_comp_assoc, lift_snd,
      ← intervalMappingUncurry_precomp, Category.comp_id]
  let h := leftFibration_lift_prism p V s.square (Vp.trans s.zero.symm)
  let W := h.choose
  have W₀ : prismEndpoint 0 (Δ[1] ⊗ P) ≫ W = V := h.choose_spec.1
  have Wp : W ≫ p = s.square := h.choose_spec.2
  let U := prismEndpoint 1 (Δ[1] ⊗ P) ≫ W
  have Up : U ≫ p = intervalMappingUncurry s.top := by
    dsimp only [U]
    rw [Category.assoc, Wp, s.one]
  have hL : (prismEndpoint 0 P ≫ U) ≫ p = SSet.const c := by
    rw [Category.assoc, Up]
    exact intervalMappingUncurry_zero s.top
  have hG : (prismEndpoint 1 P ≫ U) ≫ p = SSet.const d := by
    rw [Category.assoc, Up]
    exact intervalMappingUncurry_one s.top
  let L := vertexFiberLift p c (prismEndpoint 0 P ≫ U) hL
  let G := vertexFiberLift p d (prismEndpoint 1 P ≫ U) hG
  have Lι : L ≫ vertexFiberι p c = prismEndpoint 0 P ≫ U := vertexFiberLift_ι _ _ _ _
  have Gι : G ≫ vertexFiberι p d = prismEndpoint 1 P ≫ U := vertexFiberLift_ι _ _ _ _
  have hex (i j : Fin 2) : prismEndpoint i P ≫ (Δ[1] ◁ prismEndpoint j P) =
      prismEndpoint j P ≫ prismEndpoint i (Δ[1] ⊗ P) := rfl
  let WL := (Δ[1] ◁ prismEndpoint 0 P) ≫ W
  have WL₀ : prismEndpoint 0 P ≫ WL = f ≫ vertexFiberι p a := by
    dsimp only [WL]
    rw [← Category.assoc, hex, Category.assoc, W₀, V₀]
  have WL₁ : prismEndpoint 1 P ≫ WL = L ≫ vertexFiberι p c := by
    dsimp only [WL]
    rw [← Category.assoc, hex, Category.assoc]
    exact Lι.symm
  have WLp : WL ≫ p = intervalMappingUncurry s.left := by
    dsimp only [WL]
    rw [Category.assoc, Wp, s.inner_zero]
  let WR := (Δ[1] ◁ prismEndpoint 1 P) ≫ W
  have WR₀ : prismEndpoint 0 P ≫ WR =
      diagonalFiberTransport p f s.bottom ≫ vertexFiberι p b := by
    dsimp only [WR]
    rw [← Category.assoc, hex, Category.assoc, W₀, V₁]
  have WR₁ : prismEndpoint 1 P ≫ WR = G ≫ vertexFiberι p d := by
    dsimp only [WR]
    rw [← Category.assoc, hex, Category.assoc]
    exact Gι.symm
  have WRp : WR ≫ p = intervalMappingUncurry s.right := by
    dsimp only [WR]
    rw [Category.assoc, Wp, s.inner_one]
  have eL := leftFibrationPrism_transportIntervalIso p f L s.left WL WL₀ WL₁ WLp
  have eR := leftFibrationPrism_transportIntervalIso p
    (diagonalFiberTransport p f s.bottom) G s.right WR WR₀ WR₁ WRp
  have eU := leftFibrationPrism_transportIntervalIso p L G s.top U Lι.symm Gι.symm Up
  exact eR.symm ≪≫ eU ≪≫ diagonalFiberTransport_sourceIso p eL s.top

end SerrePositivity.InfinityCategories
