module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepresentableModulePrecomposeAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEqualityTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteCellSimultaneousPrimitives

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 等式で共通化した有限族の閉元に、同じ実閉分母を各指定始域へ輸送した後の原始元がある。 -/
theorem dgFiniteCellGraded_exists_transportedSource_primitives (P : Set D) {m : ℕ}
    (x : D) (y : Fin m → D) (hy : ∀ i, y i = x) (M : Fin m → _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D)
    (hM : ∀ i, _root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj (M i)))
    (n k : Fin m → ℤ) (hkn : ∀ i, k i + 1 = n i)
    (f : ∀ i, _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.representable A (y i))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (M i)) (n i))
    (hf : ∀ i, _root_.SerrePositivity.DifferentialGraded.differential A (f i) = 0) :
    ∃ (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
        ∀ i, ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.representable A q)
            (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (M i)) (k i),
          (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (_root_.SerrePositivity.DifferentialGraded.representable A q) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (M i))).d
            (k i) (n i) h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (n i) (f i)
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (hy i).symm) := by
  let u (i : Fin m) : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (y i) :=
    eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)) (hy i).symm)
  let f' i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D (n i) (f i) (u i)
  have hf' i : _root_.SerrePositivity.DifferentialGraded.differential A (f' i) = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose_closed A D (n i) (f i) (hf i) (u i)
  obtain ⟨q, s, hs, h⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteCellGraded_exists_simultaneous_closedPrimitives A D P x
    M hM n k hkn f' hf'
  refine ⟨q, s, hs, fun i => ?_⟩
  obtain ⟨a, da⟩ := h i
  exact ⟨a, da.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose_comp A D (n i) (f i) s (u i))⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
