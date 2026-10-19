module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismTransportCylinder

/-!
概要：任意の指定済み prism 比較円柱の終点を、元の輸送比較同型の類として計算する。
方針：底・初期値固定の同じデータへ、相対延長の終点の類の一意性を適用する。
規約：比較円柱を新たに選び直さない。使われ方：係数変更による既存比較円柱の制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b : B _⦋0⦌} (e : B.Edge a b) (f : A ⟶ vertexFiber p a)
  (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
  (hH₀ : prismEndpoint 0 A ≫ H = f ≫ vertexFiberι p a)
  (hHp : H ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
  (D : PrismTransportCylinder p e f H)
  (g : A ⟶ vertexFiber p b) (hH₁ : prismEndpoint 1 A ≫ H = g ≫ vertexFiberι p b)

/-- 同じ実際の相対円柱を終点で評価した、元の族から標準輸送への比較。 -/
def prismCylinderEndpointHomotopy : SSet.Homotopy g (f ≫ edgeTransport p e) :=
  constantBaseEndpointHomotopy p
    (fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
    D.homotopy
    (by simpa only [Category.assoc] using D.projection)
    (prismEndpoint 1 A) b
    ((prismEdgeFamily_one e.edge).trans (congrArg (fun z ↦ (SSet.const z : A ⟶ B)) e.tgt_eq))
    g (f ≫ edgeTransport p e) hH₁ (prismTransportStandard_one p e f)

/-- 終点比較の円柱は、底と初期値を保つ同じ円柱をそのまま制限したもの。 -/
lemma prismCylinderEndpointHomotopy_projection :
    (prismCylinderEndpointHomotopy p e f H D g hH₁).h ≫ vertexFiberι p b =
      (prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫
        D.homotopy.h :=
  constantBaseEndpointHomotopy_projection _ _ _ _ _ _ _ _ _ _ _

/-- この実際の円柱の終点の類は、既存の prism 輸送比較同型の射そのもの。 -/
lemma prismCylinderEndpointHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (prismCylinderEndpointHomotopy p e f H D g hH₁)) =
      (leftFibrationPrism_transportIso p e f g H hH₀ hH₁ hHp).hom := by
  let β := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge
  let i := scaffoldFirstVertex 1 ▷ A
  let v := snd (Δ[0] : SSet.{u}) A ≫ f ≫ vertexFiberι p a
  have hHi : i ≫ H = v := by
    dsimp only [i, v]
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
    change snd Δ[0] A ≫ prismEndpoint 0 A ≫ H = _
    rw [hH₀]
  have hWi : i ≫ prismTransportStandard p e f = v := by
    dsimp only [i, v]
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
    change snd Δ[0] A ≫ prismEndpoint 0 A ≫ prismTransportStandard p e f = _
    rw [prismTransportStandard_zero]
  have hv : v ≫ p = i ≫ β := by rw [← hHi, Category.assoc, hHp]
  have hj : prismEndpoint 1 A ≫ β = SSet.const b :=
    (prismEdgeFamily_one e.edge).trans (congrArg (fun z ↦ (SSet.const z : A ⟶ B)) e.tgt_eq)
  exact fixedExtensionEndpointHomotopy_hom p β i (simplexPrismFirstVertex_leftAnodyne 1 A)
    v hv (prismEndpoint 1 A) b hj H (prismTransportStandard p e f)
    hHp (prismTransportStandard_projection p e f) hHi hWi
    g (f ≫ edgeTransport p e) hH₁ (prismTransportStandard_one p e f)
    D.homotopy
    (by simpa only [Category.assoc] using D.projection)
    (by simpa only [Category.assoc] using D.initial)


end
end SerrePositivity.InfinityCategories.HomotopyLimits
