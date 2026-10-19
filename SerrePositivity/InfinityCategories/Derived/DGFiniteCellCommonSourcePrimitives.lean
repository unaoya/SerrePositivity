module
public import SerrePositivity.InfinityCategories.Derived.DGRepresentableModulePrecomposeAlgebra
public import SerrePositivity.InfinityCategories.Derived.DGClosedEqualityTransport
public import SerrePositivity.InfinityCategories.Derived.DGFiniteCellSimultaneousPrimitives

/-! # 等式で共通化された代表始域の有限族の同時原始元

概要：始対象が共通対象と等しい有限族の閉元に、一つの実閉分母後の原始元を同時供給する。
方針：等式輸送射の閉前合成で共通始域へ揃え、同時原始元を元の指定合成へ戻す。
規約：各輸送分母の実辺は同じ共通分母。使われ方：実図式辺の残差の有限同時消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 等式で共通化した有限族の閉元に、同じ実閉分母を各指定始域へ輸送した後の原始元がある。 -/
theorem dgFiniteCellGraded_exists_transportedSource_primitives (P : Set D) {m : ℕ}
    (x : D) (y : Fin m → D) (hy : ∀ i, y i = x) (M : Fin m → ModuleCategory A D)
    (hM : ∀ i, derivedFiniteCellOver A D P ((moduleToDerived A D).obj (M i)))
    (n k : Fin m → ℤ) (hkn : ∀ i, k i + 1 = n i)
    (f : ∀ i, GradedHom A (representable A (y i))
      (ForgetEnrichment.to (Complex A) (M i)) (n i))
    (hf : ∀ i, differential A (f i) = 0) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
        ∀ i, ∃ h : GradedHom A (representable A q)
            (ForgetEnrichment.to (Complex A) (M i)) (k i),
          (moduleHom A D (representable A q) (ForgetEnrichment.to (Complex A) (M i))).d
            (k i) (n i) h = dgRepresentableModulePrecompose A D (n i) (f i)
              (dgClosedTargetTransport A D s (hy i).symm) := by
  let u (i : Fin m) : ForgetEnrichment.of (Complex A) x ⟶
      ForgetEnrichment.of (Complex A) (y i) :=
    eqToHom (congrArg (ForgetEnrichment.of (Complex A)) (hy i).symm)
  let f' i := dgRepresentableModulePrecompose A D (n i) (f i) (u i)
  have hf' i : differential A (f' i) = 0 :=
    dgRepresentableModulePrecompose_closed A D (n i) (f i) (hf i) (u i)
  obtain ⟨q, s, hs, h⟩ := dgFiniteCellGraded_exists_simultaneous_closedPrimitives A D P x
    M hM n k hkn f' hf'
  refine ⟨q, s, hs, fun i => ?_⟩
  obtain ⟨a, da⟩ := h i
  exact ⟨a, da.trans (dgRepresentableModulePrecompose_comp A D (n i) (f i) s (u i))⟩

end SerrePositivity.InfinityCategories
