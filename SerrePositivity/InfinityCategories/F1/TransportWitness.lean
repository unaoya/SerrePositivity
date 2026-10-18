module

public import SerrePositivity.InfinityCategories.F1.TransportComparison

/-!
概要：cocartesian な prism を証人とする transport の分類と一意性。
方針：任意の証人を可縮な選択空間の頂点へ戻し、終点写像で比較する。
規約：証人の垂直辺には相対的な cocartesian 性を課す。
使われ方：Kerodon Definition 5.2.2.4、Proposition 5.2.2.8。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した辺に沿う cocartesian な transport の証人が存在するという性質。
方針：始点・終点・底の辺の族を固定した prism を存在量化する。
規約：垂直辺には大域的な cocartesian 性を課す。
使われ方：Kerodon Definition 5.2.2.4、cocartesian fibration で構成した transport の記述。 -/
def IsCocartesianTransport {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (F : vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e)) : Prop :=
  ∃ H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X,
    prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e) ∧
    prismEndpoint 1 _ ≫ H = F ≫ vertexFiberι p (B.δ 0 e) ∧
    H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e ∧
    ∀ v : (vertexFiber p (B.δ 1 e)) _⦋0⦌, IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))

/-- 概要：cocartesian な prism を transport の選択空間の頂点へ戻す。
方針：curry した射を cocartesian path の全部分複体に持ち上げる。
規約：終点関手の選択を入力せず、prism 全体を保持する。
使われ方：Kerodon Proposition 5.2.2.8、任意の証人と可縮な選択空間の接続。 -/
noncomputable def transportChoiceOfPrism {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e))
    (hb : H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e)
    (hc : ∀ v : (vertexFiber p (B.δ 1 e)) _⦋0⦌, IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) :
    (transportChoiceSpace p e) _⦋0⦌ := by
  have hv : ∀ v, IsCocartesianPathVertex p ((curry H).app (Opposite.op ⦋0⦌) v) := by
    intro v
    unfold IsCocartesianPathVertex
    rw [intervalFunctorVertexEdge_curry]
    exact hc v
  let a := fullSubcomplexLift (IsCocartesianPathVertex p) (curry H) hv
  have ha : a ≫ cocartesianPathι p = curry H := fullSubcomplexLift_ι _ _ _
  have has : a ≫ cocartesianPathSource p = transportSourceDiagram p e := by
    apply pullback.hom_ext
    · simp only [cocartesianPathSource, relativeEdgeSource, transportSourceDiagram,
        Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, ha, curry_evaluateFunctorAt_interval, h₀]
    · simp only [cocartesianPathSource, relativeEdgeSource, transportSourceDiagram,
        Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, ha, ← curry_natural_right, hb]
  exact cocartesianLiftSpaceVertexEquiv p (transportSourceDiagram p e) ⟨a, has⟩

/-- 概要：prism から得た選択を復元すると元の curry した prism となる。
方針：選択空間の頂点同値の両逆と全部分複体への lift の包含を使う。
規約：証人の高次単体を保持する。
使われ方：Kerodon Proposition 5.2.2.8、任意の transport の比較。 -/
lemma transportChoiceOfPrism_lift {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e))
    (hb : H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e)
    (hc : ∀ v : (vertexFiber p (B.δ 1 e)) _⦋0⦌, IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) :
    (transportChoiceLift p e (transportChoiceOfPrism p e H h₀ hb hc)).val ≫
      cocartesianPathι p = curry H := by
  simp only [transportChoiceLift, transportChoiceOfPrism, Equiv.symm_apply_apply]
  exact fullSubcomplexLift_ι _ _ _

/-- 概要：任意の transport の証人から得た選択の終点関手は元の関手。
方針：終点 fiber の包含で比較し、prism の終点条件を使う。
規約：等しいのは単体集合の射そのもの。
使われ方：Kerodon Proposition 5.2.2.8、選択空間の比較を任意の transport に適用する。 -/
lemma transportAtChoice_ofPrism {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (F : vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e))
    (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e))
    (h₁ : prismEndpoint 1 _ ≫ H = F ≫ vertexFiberι p (B.δ 0 e))
    (hb : H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e)
    (hc : ∀ v : (vertexFiber p (B.δ 1 e)) _⦋0⦌, IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) :
    transportAtChoice p e (transportChoiceOfPrism p e H h₀ hb hc) = F := by
  apply (cancel_mono (vertexFiberι p (B.δ 0 e))).1
  simp only [transportAtChoice, vertexFiberLift_ι, cocartesianPathEndpoint]
  rw [← Category.assoc, transportChoiceOfPrism_lift, curry_evaluateFunctorAt_interval]
  exact h₁

/-- 概要：cocartesian な証人を持つ二つの transport 関手は同型。
方針：それぞれの証人を選択空間へ戻し、可縮性による比較を適用する。
規約：同型は終点 fiber の関手単体集合のホモトピー圏の同型。
使われ方：Kerodon Proposition 5.2.2.8、transport の一意性。 -/
lemma IsCocartesianTransport.functorIso {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌)
    {F G : vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e)}
    (hF : IsCocartesianTransport p e F) (hG : IsCocartesianTransport p e G) :
    Nonempty (FunctorIso F G) := by
  obtain ⟨H, h₀, h₁, hb, hc⟩ := hF
  obtain ⟨K, k₀, k₁, kb, kc⟩ := hG
  rw [← transportAtChoice_ofPrism p e F H h₀ h₁ hb hc,
    ← transportAtChoice_ofPrism p e G K k₀ k₁ kb kc]
  exact ⟨transportAtChoiceIso p e _ _⟩

end SerrePositivity.InfinityCategories
