module

public import SerrePositivity.InfinityCategories.F1.TransportWitness
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyPrism

/-!
概要：同じ始点と底を持つ coCartesian prism の終点を比較する。
方針：輸送の持ち上げ空間の可縮 Kan 性を使う。
規約：パラメータに quasicategory 性を要求しない。使われ方：元の左 cf 置換の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 同じ始点と底を持つ二つの coCartesian 輸送の終点は自然同型。 -/
lemma cocartesianPrism_targetFunctorIso {A E B : SSet.{u}}
    (p : E ⟶ B) [CocartesianFibration p] (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (h0 : prismEndpoint 0 A ≫ H = prismEndpoint 0 A ≫ K)
    (hp : H ≫ p = K ≫ p)
    (hH : ∀ v : A _⦋0⦌, IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1)))
    (hK : ∀ v : A _⦋0⦌, IsCocartesianEdge p
      (K.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) :
    Nonempty (FunctorIso (prismEndpoint 1 A ≫ H) (prismEndpoint 1 A ≫ K)) := by
  have hvH : ∀ v, IsCocartesianPathVertex p ((curry H).app (Opposite.op ⦋0⦌) v) := by
    intro v
    unfold IsCocartesianPathVertex
    rw [intervalFunctorVertexEdge_curry]
    exact hH v
  have hvK : ∀ v, IsCocartesianPathVertex p ((curry K).app (Opposite.op ⦋0⦌) v) := by
    intro v
    unfold IsCocartesianPathVertex
    rw [intervalFunctorVertexEdge_curry]
    exact hK v
  let a := fullSubcomplexLift (IsCocartesianPathVertex p) (curry H) hvH
  let b := fullSubcomplexLift (IsCocartesianPathVertex p) (curry K) hvK
  have ha : a ≫ cocartesianPathι p = curry H := fullSubcomplexLift_ι _ _ _
  have hb : b ≫ cocartesianPathι p = curry K := fullSubcomplexLift_ι _ _ _
  let c := a ≫ cocartesianPathSource p
  have hc : b ≫ cocartesianPathSource p = c := by
    apply pullback.hom_ext
    · simp only [c, cocartesianPathSource, relativeEdgeSource, Category.assoc,
        pullback.lift_fst]
      rw [← Category.assoc, hb, ← Category.assoc, ha,
        curry_evaluateFunctorAt_interval, curry_evaluateFunctorAt_interval, h0]
    · simp only [c, cocartesianPathSource, relativeEdgeSource, Category.assoc,
        pullback.lift_snd]
      rw [← Category.assoc, hb, ← Category.assoc, ha,
        ← curry_natural_right, ← curry_natural_right, hp]
  let x := cocartesianLiftSpaceVertexEquiv p c ⟨a, rfl⟩
  let y := cocartesianLiftSpaceVertexEquiv p c ⟨b, hc⟩
  let q := vertexFiberι ((ihom A).map (cocartesianPathSource p)) (functorVertex c) ≫
    (ihom A).map (cocartesianPathEndpoint p 1)
  have hx : q.app (Opposite.op ⦋0⦌) x = functorVertex (prismEndpoint 1 A ≫ H) := by
    change functorVertex (a ≫ cocartesianPathEndpoint p 1) = _
    congr 1
    dsimp only [cocartesianPathEndpoint]
    rw [← Category.assoc, ha, curry_evaluateFunctorAt_interval]
  have hy : q.app (Opposite.op ⦋0⦌) y = functorVertex (prismEndpoint 1 A ≫ K) := by
    change functorVertex (b ≫ cocartesianPathEndpoint p 1) = _
    congr 1
    dsimp only [cocartesianPathEndpoint]
    rw [← Category.assoc, hb, curry_evaluateFunctorAt_interval]
  have hiso := ((cocartesianLiftSpace_isContractibleKan p c).vertexIso x y).map q
  exact ⟨(eqToIso (congrArg HomotopyCategory.mk hx)).symm ≪≫ hiso ≪≫
    eqToIso (congrArg HomotopyCategory.mk hy)⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
