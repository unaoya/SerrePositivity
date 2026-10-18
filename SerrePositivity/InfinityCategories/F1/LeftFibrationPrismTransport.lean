module

public import SerrePositivity.InfinityCategories.F1.LeftFibrationTransportNaturality

/-!
概要：任意の係数空間からの prism と left fibration の標準 transport の比較。
方針：与えた prism と標準 transport の引き戻しを同じ初期値の相対延長として比較する。
規約：係数空間の Kan 性を要求しない。
使われ方：Kerodon Proposition 5.2.2.8、Corollary 5.6.0.6、coherent な係数の作用と fiber transport の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した辺を被覆する prism の終点は初期値と標準 transport の合成と関手同型。
方針：標準 transport の証人を初期値で引き戻し、可縮な相対延長空間の終点を比較する。
規約：初期値と終点は同じ係数空間 A から各 fiber への射として指定する。
使われ方：Kerodon Proposition 5.2.2.8、Corollary 5.6.0.6、weighted nerve の比較 prism の評価。 -/
noncomputable def leftFibrationPrism_transportIso {A E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (f : A ⟶ vertexFiber p a) (g : A ⟶ vertexFiber p b)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hH₀ : prismEndpoint 0 A ≫ H = f ≫ vertexFiberι p a)
    (hH₁ : prismEndpoint 1 A ≫ H = g ≫ vertexFiberι p b)
    (hHp : H ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge) :
    FunctorIso g (f ≫ edgeTransport p e) := by
  let K := (edgeTransport_isTransport p e).choose
  have hK₀ := (edgeTransport_isTransport p e).choose_spec.1
  have hK₁ := (edgeTransport_isTransport p e).choose_spec.2.1
  have hKp := (edgeTransport_isTransport p e).choose_spec.2.2.1
  let β := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge
  let i := scaffoldFirstVertex 1 ▷ A
  let v := snd (Δ[0] : SSet.{u}) A ≫ f ≫ vertexFiberι p a
  let W := (Δ[1] ◁ f) ≫ K
  have hW : W ≫ p = β := by
    dsimp only [W, β]
    rw [Category.assoc, hKp, ← Category.assoc, whiskerLeft_fst]
    rfl
  have hW₀ : prismEndpoint 0 A ≫ W = f ≫ vertexFiberι p a := by
    dsimp only [W]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hK₀]
  have hHi : i ≫ H = v := by
    dsimp only [i, v]
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
    exact congrArg (fun z ↦ snd (Δ[0] : SSet.{u}) A ≫ z) hH₀
  have hWi : i ≫ W = v := by
    dsimp only [i, v]
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
    exact congrArg (fun z ↦ snd (Δ[0] : SSet.{u}) A ≫ z) hW₀
  have hv : v ≫ p = i ≫ β := by rw [← hHi, Category.assoc, hHp]
  have hj : prismEndpoint 1 A ≫ β = SSet.const b :=
    (prismEdgeFamily_one e.edge).trans (congrArg (fun z ↦ (SSet.const z : A ⟶ B)) e.tgt_eq)
  have hW₁ : prismEndpoint 1 A ≫ W = (f ≫ edgeTransport p e) ≫ vertexFiberι p b := by
    dsimp only [W]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hK₁, Category.assoc]
  exact relativeExtensionFiberEndpoint_witnessIso p β i
    (simplexPrismFirstVertex_leftAnodyne 1 A) v hv (prismEndpoint 1 A) b hj H W hHp hW
    hHi hWi g (f ≫ edgeTransport p e) hH₁ hW₁

end SerrePositivity.InfinityCategories
