module

public import SerrePositivity.InfinityCategories.F1.Transport.FiberTransportFamilySourceComparison
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：指定始点からの全パラメータ付き持ち上げの終値を、同じ点からの普遍輸送と比較する。
方針：一点を係数とする輸送族にし、元の全族の選択独立性を一点で評価する。
規約：頂点ごとでなく、全パラメータ上の一つの関手同型。
使われ方：恒等点復元射上の密度持ち上げを canonical な輸送へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ底の区間族・同じ始点の持ち上げの終値は、同じ点からの普遍輸送と関手同型。 -/
def pointPrismTransportIso {E B L : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (v : (vertexFiber p a) _⦋0⦌) (f : L ⟶ intervalMappingSpace a b)
    (W : (Δ[1] : SSet.{u}) ⊗ L ⟶ E) (q : L ⟶ vertexFiber p b)
    (h₀ : prismEndpoint 0 L ≫ W = SSet.const v.val)
    (h₁ : prismEndpoint 1 L ≫ W = q ≫ vertexFiberι p b)
    (hp : W ≫ p = intervalMappingUncurry f) :
    FunctorIso q (f ≫ parametrizedFiberTransport p a b ≫ evaluateFunctorAt v) := by
  let V : (Δ[0] : SSet.{u}) ⟶ vertexFiber p a := SSet.const v
  let T : FiberTransportFamily (b := b) p V (intervalMappingUncurry f) :=
    { endpoint := snd Δ[0] L ≫ q
      prism := (Δ[1] ◁ snd Δ[0] L) ≫ W
      start := by
        rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₀]
        simp only [SSet.comp_const, Category.assoc, SSet.const_comp]
        rfl
      finish := by
        rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₁,
          Category.assoc]
      over_base := by rw [Category.assoc, hp] }
  have he := FunctorIso.postcomp (T.mapIso_parametrizedSource p V _
    (intervalMappingUncurry_zero f) (intervalMappingUncurry_one f))
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  have hq : T.map ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = q := by
    change curry (snd Δ[0] L ≫ q) ≫ evaluateFunctorAt _ = q
    rw [curry_evaluateFunctorAt_vertex, ← Category.assoc, lift_snd, Category.id_comp]
  have hf : intervalMappingCurryOfEndpoints (intervalMappingUncurry f)
      (intervalMappingUncurry_zero f) (intervalMappingUncurry_one f) = f := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [hq, hf] at he
  have hv : V.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = v := by
    change PinchedHom.constant v 0 = v
    exact pinchedConstant_zero v
  simpa only [Category.assoc, evaluateFunctorAt_pre, hv] using he

end SerrePositivity.InfinityCategories.F2.Ind
