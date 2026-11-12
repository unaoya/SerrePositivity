module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportDiagonalPrismCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra

/-!
概要：元の全対角輸送比較を、元の実 prism による同じ指定比較として表示する。
方針：元の定義の区間頂点の表示変更だけを除去する。
規約：指定比較を選び直さない。使われ方：固定射の全値比較と元の長辺比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {P E B K L : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (f : K ⟶ vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
  (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
  (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
  (T : FiberTransportFamily (b := b) p f γ) (x : P ⟶ K) (y : P ⟶ L)
local notation "v" => y ≫ intervalMappingCurryOfEndpoints γ h₀ h₁

/-- 元の全対角輸送の指定同型は、元の実二 prism を比較する同じ指定同型。 -/
lemma fiberTransportDiagonalIso_heq_prism :
    HEq (T.diagonalIso p f γ h₀ h₁ x y)
      (leftFibrationPrism_diagonalTransportIso p (x ≫ f) (lift x y ≫ T.endpoint)
        (intervalMappingUncurry v) (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v)
        ((Δ[1] ◁ lift x y) ≫ T.prism)
        (fiberTransportDiagonalPrism_start p f γ T x y)
        (fiberTransportDiagonalPrism_finish p f γ T x y)
        (fiberTransportDiagonalPrism_projection p f γ h₀ h₁ T x y)) := by
  unfold FiberTransportFamily.diagonalIso
  change HEq (Eq.mp _ _) _
  have hcast {α β : Sort (u + 1)} (h : α = β) (z : α) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  exact hcast _ _

/-- 同じ全対角比較の値の係数制限も、同じ実 prism の指定比較の値を保持する。 -/
lemma fiberTransportDiagonalIso_postcomp_precomp_heq_prism {Q Z : SSet.{u}}
    (q : vertexFiber p b ⟶ Z) (r : Q ⟶ P) :
    HEq (((T.diagonalIso p f γ h₀ h₁ x y).postcomp q).precomp r)
      (((leftFibrationPrism_diagonalTransportIso p (x ≫ f) (lift x y ≫ T.endpoint)
        (intervalMappingUncurry v) (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v)
        ((Δ[1] ◁ lift x y) ≫ T.prism)
        (fiberTransportDiagonalPrism_start p f γ T x y)
        (fiberTransportDiagonalPrism_finish p f γ T x y)
        (fiberTransportDiagonalPrism_projection p f γ h₀ h₁ T x y)).postcomp q).precomp r) := by
  let e := leftFibrationPrism_diagonalTransportIso p (x ≫ f) (lift x y ≫ T.endpoint)
    (intervalMappingUncurry v) (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v)
    ((Δ[1] ◁ lift x y) ≫ T.prism)
    (fiberTransportDiagonalPrism_start p f γ T x y)
    (fiberTransportDiagonalPrism_finish p f γ T x y)
    (fiberTransportDiagonalPrism_projection p f γ h₀ h₁ T x y)
  have hv : intervalMappingCurryOfEndpoints (intervalMappingUncurry v)
      (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v) = v := by
    apply intervalMappingUncurry_injective _ _
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  have hg := congrArg (diagonalFiberTransport p (x ≫ f)) hv
  have he := functorIso_postcomp_heq_of_heq e (T.diagonalIso p f γ h₀ h₁ x y) rfl hg
    (fiberTransportDiagonalIso_heq_prism p f γ h₀ h₁ T x y) q
  exact functorIso_precomp_heq_of_heq (e.postcomp q)
    ((T.diagonalIso p f γ h₀ h₁ x y).postcomp q) rfl
    (congrArg (fun h ↦ h ≫ q) hg) he r

end SerrePositivity.InfinityCategories.F2
