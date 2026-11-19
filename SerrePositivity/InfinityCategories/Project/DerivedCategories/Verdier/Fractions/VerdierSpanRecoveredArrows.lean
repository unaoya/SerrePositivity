module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ArrowFamilyRecoveredEdge
public import SerrePositivity.KST.LocalizingInvariants.ArrowFamilyRecoveredEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSpanFamilyHomotopy

/-!
概要：共通実分母と実次辺の商像を、パラメータ関手圏の同じ固定端点の実辺にする。
方針：実次辺の両端と同じ元の分母を回収し、固定端点の全辺族の転置を適用する。
規約：分母・分子とも元の一次単体を保持し、同値類の代表選択はしない。
使われ方：分数比較四角形の合成整合を前段・次辺の貼合せへ代入する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
  (x y : B.obj _⦋0⦌) (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌)
  {K : SSet.{u}} (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d)

/-- 同じ実次辺の全族を商後合成した実辺族。 -/
def verdierSpanMappedNumeratorFamily : K ⟶ (ihom (Δ[1] : SSet.{u})).obj C.obj :=
  g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFiberArrow i x y d ≫ (ihom (Δ[1] : SSet.{u})).map q.hom

lemma verdierSpanMappedNumeratorFamily_source : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorFamily i q x y d g ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C.obj) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    SSet.const (q.hom.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorOverSource i x).app (Opposite.op ⦋0⦌) d)) := by
  have hn : (ihom (Δ[1] : SSet.{u})).map q.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C.obj) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫ q.hom := rfl
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorFamily, Category.assoc, Category.assoc, hn,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFiberArrow i x y d),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFiberArrow_source, SSet.const_comp, SSet.comp_const]

lemma verdierSpanMappedNumeratorFamily_target : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorFamily i q x y d g ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C.obj) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.const (q.hom.app (Opposite.op ⦋0⦌) y) := by
  have hn : (ihom (Δ[1] : SSet.{u})).map q.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C.obj) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫ q.hom := rfl
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorFamily, Category.assoc, Category.assoc, hn,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFiberArrow i x y d),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFiberArrow_target, SSet.const_comp, SSet.comp_const]

/-- 元の実次辺族の商像を、同じ固定端点を持つパラメータ関手圏の実辺として回収する。 -/
def verdierSpanMappedNumeratorEdge :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorOverSource i x).app (Opposite.op ⦋0⦌) d)) : K ⟶ C.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌) y) : K ⟶ C.obj)) :=
  spanArrowFamilyEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorFamily i q x y d g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorFamily_source i q x y d g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorFamily_target i q x y d g)

lemma verdierSpanMappedNumeratorEdge_edge : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorEdge i q x y d g).edge =
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] C.obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorFamily i q x y d g)) :=
  spanArrowFamilyEdge_edge _ _ _

/-- 同じ元の実分母の辺を商後合成し、元の両端点を持つ実辺として回収する。 -/
def verdierSpanMappedDenominator : Truncated.Edge (X := (truncation 2).obj C.obj)
    (q.hom.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorOverSource i x).app (Opposite.op ⦋0⦌) d))
    (q.hom.app (Opposite.op ⦋0⦌) x) :=
  (((SSet.Edge.ofTruncated (X := B.obj)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x) d.val)).ofEq rfl
      (Equiv.apply_symm_apply SSet.yonedaEquiv x)).map q.hom).toTruncated

lemma verdierSpanMappedDenominator_diagram :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator i q x d).edge =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanDenominatorDiagram i q x d := by
  change SSet.yonedaEquiv.symm (q.hom.app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ d.val.val))) = _
  rw [← SSet.yonedaEquiv_comp, Equiv.symm_apply_apply]
  exact Category.assoc _ _ _

/-- 同じ実分母を全パラメータで定値にした、固定端点を持つ実関手辺。 -/
def verdierSpanMappedDenominatorEdge (K : SSet.{u}) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorOverSource i x).app (Opposite.op ⦋0⦌) d)) : K ⟶ C.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌) x) : K ⟶ C.obj)) :=
  spanArrowFamilyEdge (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator i q x d).edge)))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanConstantArrowFamily_source _) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanConstantArrowFamily_target _)

lemma verdierSpanMappedDenominatorEdge_edge (K : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominatorEdge i q x d K).edge =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanDenominatorDiagram i q x d ≫
        curry (CartesianMonoidalCategory.snd K C.obj)) := by
  have he := spanArrowFamilyEdge_edge
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator i q x d).edge)) :
      K ⟶ (ihom (Δ[1] : SSet.{u})).obj C.obj)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanConstantArrowFamily_source _) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanConstantArrowFamily_target _)
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] C.obj
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator i q x d).edge))) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanDenominatorDiagram i q x d ≫ curry (CartesianMonoidalCategory.snd K C.obj) :=
    (spanInternalHomFlip_const _).trans
      (congrArg (fun f => f ≫ curry (CartesianMonoidalCategory.snd K C.obj))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator_diagram i q x d))
  exact he.trans (congrArg SSet.yonedaEquiv hf)

/-- 同じ元の実分母は、全パラメータ関手圏でも実際に可逆な指定辺。 -/
lemma verdierSpanMappedDenominatorEdge_isInvertible (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (K : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominatorEdge i q x d K).toTruncated := by
  have hi := h.inverts (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex d)
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator i q x d) := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x) d.val).edge).map
        ((truncation 2).map q.hom)) (f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator i q x d) rfl).mp hi
  let c := curry (CartesianMonoidalCategory.snd K C.obj)
  have hdiag : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanDenominatorDiagram i q x d) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator i q x d).edge :=
    (congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator_diagram i q x d)).symm.trans
      (Equiv.apply_symm_apply _ _)
  have he : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator i q x d).map ((truncation 2).map c)).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominatorEdge i q x d K).edge := by
    calc
      _ = c.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominator i q x d).edge := rfl
      _ = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanDenominatorDiagram i q x d ≫ c) := by
        rw [SSet.yonedaEquiv_comp, hdiag]
      _ = _ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominatorEdge_edge i q x d K).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mp (hd.map c)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
