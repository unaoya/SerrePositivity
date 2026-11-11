module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportIntervalComparisonPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismComparisonPrecomp
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport

/-!
概要：元の区間表示の指定比較は、全係数を制限しても同じ実 prism 比較になる。
方針：元の対角比較の係数自然性を、curry の往復だけを外して移す。
規約：元の指定同型を保持。使われ方：実四角形の四辺比較の係数制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実区間比較の前合成は、係数制限した同じ実 prism の元の区間比較。 -/
lemma leftFibrationPrism_transportIntervalIso_precomp_heq {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b)
    (c : P ⟶ intervalMappingSpace a b) (W : Δ[1] ⊗ P ⟶ E)
    (hs : prismEndpoint 0 P ≫ W = f ≫ vertexFiberι p a)
    (he : prismEndpoint 1 P ≫ W = g ≫ vertexFiberι p b)
    (hp : W ≫ p = intervalMappingUncurry c) (q : Q ⟶ P)
    (hs' : prismEndpoint 0 Q ≫ ((Δ[1] ◁ q) ≫ W) = (q ≫ f) ≫ vertexFiberι p a)
    (he' : prismEndpoint 1 Q ≫ ((Δ[1] ◁ q) ≫ W) = (q ≫ g) ≫ vertexFiberι p b)
    (hp' : ((Δ[1] ◁ q) ≫ W) ≫ p = intervalMappingUncurry (q ≫ c)) :
    HEq ((leftFibrationPrism_transportIntervalIso p f g c W hs he hp).precomp q)
      (leftFibrationPrism_transportIntervalIso p (q ≫ f) (q ≫ g) (q ≫ c)
        ((Δ[1] ◁ q) ≫ W) hs' he' hp') := by
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry c)
      (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c) = c := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  have hpre := functorIso_precomp_heq_of_heq
    (leftFibrationPrism_diagonalTransportIso p f g (intervalMappingUncurry c)
      (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c) W hs he hp)
    (leftFibrationPrism_transportIntervalIso p f g c W hs he hp) rfl
    (congrArg (diagonalFiberTransport p f) hc)
    (leftFibrationPrism_transportIntervalIso_heq_diagonal p f g c W hs he hp) q
  have h₀ : prismEndpoint 0 Q ≫ ((Δ[1] ◁ q) ≫ intervalMappingUncurry c) =
      SSet.const a := by
    rw [← intervalMappingUncurry_precomp, intervalMappingUncurry_zero]
  have h₁ : prismEndpoint 1 Q ≫ ((Δ[1] ◁ q) ≫ intervalMappingUncurry c) =
      SSet.const b := by
    rw [← intervalMappingUncurry_precomp, intervalMappingUncurry_one]
  have hraw := leftFibrationPrism_diagonalTransportIso_precomp_heq p f g
    (intervalMappingUncurry c) (intervalMappingUncurry_zero c)
    (intervalMappingUncurry_one c) W hs he hp q h₀ h₁
  exact hpre.trans (hraw.trans (leftFibrationPrism_diagonal_heq_interval_of_base p
    (q ≫ f) (q ≫ g) ((Δ[1] ◁ q) ≫ intervalMappingUncurry c) h₀ h₁
    ((Δ[1] ◁ q) ≫ W) hs' he'
    (by rw [Category.assoc, hp]) (q ≫ c) (intervalMappingUncurry_precomp q c).symm))

end SerrePositivity.InfinityCategories.F2
