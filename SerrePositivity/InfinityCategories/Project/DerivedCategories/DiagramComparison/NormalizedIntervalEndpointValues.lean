module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalVertexValues
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalEndpoints
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexCochainAugmentationZero
/-!
概要：指定区間端点の零次値を同じ頂点生成元と照合する。
方針：零単体の増大写像の逆と正規化の自然性を評価する。
規約：A06端点等式の証明分割。別の区間同型を追加しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
/-- 元の頂点包含は同じ零次生成元を指定頂点へ送る。 -/
theorem normalizedIntervalVertexGenerator_map (ε : Fin 2) :
    ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
      (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ ε))).f 0
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A) = normalizedIntervalVertexGenerator A ε := by
  let W := (SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
    (SSet.stdSimplex.obj ⦋0⦌)
  let V := (SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
    (SSet.stdSimplex.obj ⦋1⦌)
  let t := (SerrePositivity.EInfinity.BarrattEccles.linearization A).map
    (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ ε))
  change (extendMap ((normalizedMooreComplex (ModuleCat A)).map t)
    ComplexShape.embeddingDownNat).f 0 _ = _
  rw [extendMap_f _ _ (i := 0) (i' := (0 : ℤ)) rfl]
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  have h := ConcreteCategory.congr_hom (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso_inv_naturality t)
    (_root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator A ⦋0⦌)
  simp only [ModuleCat.comp_apply] at h
  rw [← h]
  dsimp only [t, SerrePositivity.EInfinity.BarrattEccles.linearization,
    Functor.whiskeringRight, Functor.comp_map, _root_.SerrePositivity.ComplexLimits.linearizedSimplexGenerator]
  erw [ModuleCat.free_map_apply]
  rfl
/-- 指定端点の単位の値は同じ指定頂点生成元。 -/
theorem normalizedIntervalEndpointChain_value (ε : Fin 2) :
    (normalizedIntervalEndpointChain A ε).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
        normalizedIntervalVertexGenerator A ε := by
  let c := (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A ⦋0⦌).hom
  letI : IsIso c := by
    dsimp only [c]
    rw [← _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_stdSimplex_eq_contraction]
    exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_stdSimplexZero_isIso A
  have hc : c.f 0 (_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
    apply (ModuleCat.mono_iff_injective
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom).mp inferInstance
    rw [Iso.inv_hom_id_apply]
    exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainAugmentation_zero_generator A
  have hi : ((asIso c).inv).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
      _root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A := by
    rw [← hc]
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.f 0) (asIso c).hom_inv_id) (_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A)
  change ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
    (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ ε))).f 0
      (((asIso c).inv).f 0 _) = _
  rw [hi]
  exact normalizedIntervalVertexGenerator_map A ε
/-- 同じ区間写像の両端は指定した閉零次値からの単位射になる。 -/
theorem normalizedIntervalCochainMapOfBoundary_endpoints
    (H : CochainComplex (ModuleCat.{u} A) ℤ)
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) :
    normalizedIntervalEndpointChain A 0 ≫
      normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw =
        SerrePositivity.DifferentialGraded.unitFromCycle H ⟨x, hx⟩ ∧
    normalizedIntervalEndpointChain A 1 ≫
      normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw =
        SerrePositivity.DifferentialGraded.unitFromCycle H ⟨y, hy⟩ := by
  constructor
  · apply (SerrePositivity.DifferentialGraded.unitCycleEquiv H).injective
    apply Subtype.ext
    change (SerrePositivity.DifferentialGraded.cycleFromUnit H _).val =
      (SerrePositivity.DifferentialGraded.cycleFromUnit H
        (SerrePositivity.DifferentialGraded.unitFromCycle H ⟨x, hx⟩)).val
    rw [SerrePositivity.DifferentialGraded.cycleFromUnit_unitFromCycle]
    change (normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw).f 0
      ((normalizedIntervalEndpointChain A 0).f 0 _) = x
    rw [normalizedIntervalEndpointChain_value, normalizedIntervalCochainMapOfBoundary_vertex]
    rfl
  · apply (SerrePositivity.DifferentialGraded.unitCycleEquiv H).injective
    apply Subtype.ext
    change (SerrePositivity.DifferentialGraded.cycleFromUnit H _).val =
      (SerrePositivity.DifferentialGraded.cycleFromUnit H
        (SerrePositivity.DifferentialGraded.unitFromCycle H ⟨y, hy⟩)).val
    rw [SerrePositivity.DifferentialGraded.cycleFromUnit_unitFromCycle]
    change (normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw).f 0
      ((normalizedIntervalEndpointChain A 1).f 0 _) = y
    rw [normalizedIntervalEndpointChain_value, normalizedIntervalCochainMapOfBoundary_vertex]
    rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
