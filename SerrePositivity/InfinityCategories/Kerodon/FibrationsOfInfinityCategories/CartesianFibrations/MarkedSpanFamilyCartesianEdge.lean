module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SpanFinalHornExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.MarkedSpanFamilyCocartesianEdge

/-!
概要：分母付き span 族の右脚が pullback 正方形なら、元の辺は cartesian。
方針：右脚と固定終点の左脚を充填し、全頂点をホーンから回収して分母条件を保つ。
規約：分母集合は任意。使われ方：Tamme 分母上の普遍 Ore lift の cartesian 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma isCartesianEdge_markedSpanFamilyProjection_of_pullback
    {X : SSet.{u}} [Quasicategory X] (W : Set (X _⦋1⦌)) (x : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x) _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (uncurry (SSet.yonedaEquiv.symm e ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ markedSpanInclusion X W ≫
        (pre horn₂₀.ι₀₂).app X))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) e := by
  intro m σ β hσ sq
  let r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x ⟶ (ihom (horn 2 0 : SSet.{u})).obj X :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ markedSpanInclusion X W
  let σ' : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶
      (ihom (horn 2 0 : SSet.{u})).obj X := σ ≫ r
  have hs : σ' ≫ (pre horn₂₀.ι₀₁).app X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const x := by
    change σ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ markedSpanSource X W = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  have ht : σ' ≫ (pre horn₂₀.ι₀₂).app X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ β := sq.w
  have hσr : (σ' ≫ (pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m) =
      (r ≫ (pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋1⦌) e := by
    change (r ≫ (pre horn₂₀.ι₀₂).app X).app _ (σ.app _ _) = _
    rw [hσ]
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      ((σ' ≫ (pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m)) := by
    rw [hσr]
    apply arrowTarget_isCartesianEdge_of_pullback
    rw [← SSet.yonedaEquiv_symm_comp]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (uncurry (SSet.yonedaEquiv.symm e ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ markedSpanInclusion X W ≫
        (pre horn₂₀.ι₀₂).app X))
    exact he
  obtain ⟨G, hG, hGs, hGt⟩ :=
    exists_span_finalHorn_extension_of_right_cartesian m σ' β x hs ht hc
  have hv : ∀ v : (Δ[m + 2] : SSet.{u}) _⦋0⦌,
      spanLeftEdge (G.app (Opposite.op ⦋0⦌) v) ∈ W := by
    intro v
    let w : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) _⦋0⦌ :=
      ⟨v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn m (Fin.last (m + 2)) v⟩
    have h := congrArg (fun k => k.app (Opposite.op ⦋0⦌) w) hG
    have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (σ.app (Opposite.op ⦋0⦌) w).val
    change G.app (Opposite.op ⦋0⦌) v = (σ.app (Opposite.op ⦋0⦌) w).val.val at h
    exact h.symm ▸ hp
  let M := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (fun v => spanLeftEdge v ∈ W) G hv
  have hM : M ≫ markedSpanInclusion X W = G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hMs : M ≫ markedSpanSource X W = SSet.const x := by
    change M ≫ markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₁).app X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
    rw [← Category.assoc, ← Category.assoc, hM]
    exact hGs
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (markedSpanSource X W) x M hMs
  have hF : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x = M := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hFr : F ≫ r = G := by
    dsimp only [r]
    rw [← Category.assoc, hF, hM]
  refine CommSq.HasLift.mk' { l := F, fac_left := ?_, fac_right := ?_ }
  · have : Mono r := by dsimp [r, markedSpanInclusion]; infer_instance
    apply (cancel_mono r).mp
    rw [Category.assoc, hFr]
    exact hG
  · change (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x) ≫ markedSpanTarget X W = β
    rw [hF]
    change M ≫ markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₂).app X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = β
    rw [← Category.assoc, ← Category.assoc, hM]
    exact hGt

end SerrePositivity.KST.LocalizingInvariants
