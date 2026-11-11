module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourceArrows
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexFiberSquareIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceCoconeFamilyEquivalence

/-!
概要：固定始域の余錐族を、元の始点評価の厳密な fiber に送る。
方針：一点と一点の join の左頂点を計算し、元の全余錐族の底制限を使う。
規約：源の頂点一致だけでなく全単体での定値性を保持する。
使われ方：固定始域圏と射圏の引き戻しとの比較準備。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 一点二つの join の左頂点は、元の区間の始点と厳密に一致する。 -/
lemma sourceArrow_leftVertex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) Δ[0] ≅ Δ[1]).inv.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm 0) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] Δ[0]).app _
      (SSet.yonedaEquiv (𝟙 Δ[0])) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp]
  have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i
    rfl
  rw [hv, ← SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply, Category.id_comp,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [Quasicategory C] in
/-- 元の脚の族の始点評価は、元の指定始点への厳密な定値関手。 -/
lemma sourceCosliceArrowFamily_source (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceArrowFamily x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
      SSet.const x := by
  have he := sourceArrow_leftVertex.{u}
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceArrowFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre, he,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre, ← Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorFamily (SSet.yonedaEquiv.symm x) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction Δ[0] C) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (𝟙 Δ[0])) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorFamily_restriction, SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  congr 1
  rw [← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

/-- 飽和射圏への比較の始点は、元の固定始点への定値関手に厳密に一致する。 -/
lemma generatedSourceArrows_source (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceArrows edges x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = SSet.const x := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceArrows_inclusion, Category.assoc,
    sourceCosliceArrowFamily_source, SSet.comp_const]

/-- 元の始点評価で定義した、飽和射圏の厳密な固定始域 fiber。 -/
def generatedSourceArrowFiber (edges : I → C _⦋1⦌) (x : C _⦋0⦌) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) x

/-- 元の全 coslice 部分圏から、同じ始点の厳密な射圏 fiber への比較。 -/
def generatedSourceToArrowFiber (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x ⟶ generatedSourceArrowFiber edges x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ x (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceArrows edges x) (generatedSourceArrows_source edges x)

/-- 厳密な fiber への比較も、元の同じ全余錐族からの射を保持する。 -/
lemma generatedSourceToArrowFiber_inclusion (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceToArrowFiber edges x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceArrows edges x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

omit [Quasicategory C] in
/-- 一点下の全余錐の関手模型は、元の始点評価の厳密な fiber と同型。 -/
def sourceCoconeArrowFiberIso (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamily (SSet.yonedaEquiv.symm x) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x := by
  let e : (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) Δ[0])).obj C ≅ (ihom Δ[1]).obj C :=
    { hom := (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).app C
      inv := (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app C
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id, NatTrans.id_app]
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id, NatTrans.id_app] }
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso C
  have hv0 : (stdSimplex.obj₀Equiv.symm (0 : Fin 1) : (Δ[0] : SSet.{u + 1}) _⦋0⦌) =
      SSet.yonedaEquiv (𝟙 Δ[0]) := by
    apply SSet.stdSimplex.ext
    intro i
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction Δ[0] C ≫ d.hom =
      e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌) := by
    change (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] Δ[0])).app C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).app C ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre, sourceArrow_leftVertex, hv0]
  have hx : d.hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm x)) = x := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm x)) = x
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, hv0, ← SSet.yonedaEquiv_comp,
      Category.id_comp, Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberSquareIso _ _ e d h (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm x)) ≪≫
    eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _) hx)

/-- 元の始点評価の厳密な fiber は quasicategory。 -/
instance sourceArrowFiber_quasicategory (x : C _⦋0⦌) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x) :=
  quasicategory_of_innerFibration (sourceCoconeArrowFiberIso x).inv

/-- 元の全 coslice は、元の始点評価の厳密な fiber と同値。 -/
def sourceCosliceArrowFiberEquivalence (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C)
        (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceCoconeFamilyMap (SSet.yonedaEquiv.symm x)).choose.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (sourceCoconeArrowFiberIso x))

private lemma sourceFiberEqIso_inclusion {E B : SSet.{u + 1}} (p : E ⟶ B)
    {x y : B _⦋0⦌} (h : x = y) :
    (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p y = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x := by
  cases h
  rfl

omit [Quasicategory C] in
/-- 余錐模型と元の射圏の fiber の同型は、同じ元の全射族を保持する。 -/
lemma sourceCoconeArrowFiberIso_inclusion (x : C _⦋0⦌) :
    (sourceCoconeArrowFiberIso x).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction Δ[0] C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm x)) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).app C := by
  dsimp only [sourceCoconeArrowFiberIso, Iso.trans_hom]
  rw [Category.assoc, sourceFiberEqIso_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberSquareIso_hom_inclusion]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm x)) = x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  have hv0 : (stdSimplex.obj₀Equiv.symm (0 : Fin 1) : (Δ[0] : SSet.{u + 1}) _⦋0⦌) =
      SSet.yonedaEquiv (𝟙 Δ[0]) := by
    apply SSet.stdSimplex.ext
    intro i
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
  rw [hv0, ← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

/-- 全 coslice との同値も、元の全余錐族からの射を厳密に回収する。 -/
lemma sourceCosliceArrowFiberEquivalence_inclusion (x : C _⦋0⦌) :
    (sourceCosliceArrowFiberEquivalence x).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceArrowFamily x := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceCoconeFamilyMap (SSet.yonedaEquiv.symm x) ≫
    (sourceCoconeArrowFiberIso x).hom) ≫ _ = _
  rw [Category.assoc, sourceCoconeArrowFiberIso_inclusion, ← Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
