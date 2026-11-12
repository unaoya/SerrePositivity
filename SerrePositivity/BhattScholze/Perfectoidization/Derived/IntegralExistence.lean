module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialCofinality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEdgeCompatibility
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiscreteCharacterization
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import SerrePositivity.BhattScholze.Inputs.PerfectoidizationInterface
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Completion
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# E3 から整代数の普遍 perfectoid 化へ（BS 著者版 Theorem 1.17(1)＝BS 著者版 Theorem 10.11 の環版）

## 概要
指定された普遍 perfectoid 化と導来極限の比較、始対象の値による極限錐の計算、整代数・有限代数・完備化の普遍 perfectoid 化の存在。

## 方針
E3 の limit・universal・integral 欄から環の普遍性を取り出す。

## 規約
E3 の存在を引用する。

## 使われ方
CLMST Prop 2.4.7、有限直積、almost 比較、SerrePositivity/Inputs/Perfectoidization。
-/

universe u v w

/-! ## 始対象の値による指定極限錐の計算（旧 PerfectoidizationInterface/InitialLimit.lean）

概要：二宇宙の cofinality を使い、始対象からの標準錐を極限錐にする。
方針：一点図式の恒等錐の終対象性を外側ホーンで検証し、制限で反映する。
規約：極限の比較は h(sliceOver) に保持する。
使われ方：Π2-5 の指定 perfectoid 化との比較。
-/

@[expose] public noncomputable section InitialLimit

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- 一点図式の恒等錐は slice の終対象である。 -/
theorem sliceIdentityCone_terminal {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone x) := by
  intro n b hb
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b
  let σ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso (n + 1)).inv ≫ L
  let e := SSet.Truncated.Edge.id (X := (truncation 2).obj X) x
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk e)
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have hσ : σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n) = e.edge := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso_edge, ← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso (n + 1)).hom) ≫
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso (n + 1)).inv ≫ L)) = _
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone, SSet.comp_const]
    change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x =
      X.map (SimplexCategory.σ (0 : Fin 1)).op x
    exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ => X.map α.op x) (by decide)
  obtain ⟨G, hG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge e he n σ hσ
  let M := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0).hom ≫ G
  have hM : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (boundary (n + 1)).ι (𝟙 Δ[0]) ≫ M = L := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (boundary (n + 1)).ι (𝟙 Δ[0]) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0).hom ≫ G = L
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso_hom_ι, Category.assoc, hG]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso (n + 1)).hom_inv_id_assoc L
  have hfixed : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n + 1] Δ[0] ≫ M = SSet.yonedaEquiv.symm x := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed b]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n + 1] Δ[0] ≫ M = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (boundary (n + 1) : SSet) Δ[0] ≫ L
    rw [← hM]
    simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry M hfixed, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry_precomp]
  have heq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (boundary (n + 1)).ι (𝟙 Δ[0]) ≫ M)
      (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp, hfixed]) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed b) := by
    congr 1
  exact heq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry_uncurry b)

/-- 始対象を全射列に前置して得る標準錐。 -/
def initialValueCone {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hc ≫ F, by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone_inr, Category.id_comp]⟩

/-- 始対象で制限した標準錐の射は定数射。 -/
theorem initialValueCone_restriction {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialRestriction F c).app (Opposite.op ⦋0⦌) (initialValueCone hc F)).val =
      SSet.const (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hc ≫ F) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone_at_point, SSet.const_comp]

/-- 二宇宙版の cofinality により始対象の値の標準錐が極限になる。 -/
theorem initialValueCone_isLimit {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (initialValueCone hc F) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialCofinality hc F
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialRestriction F c)
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c ≫ F = SSet.yonedaEquiv.symm (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint, SSet.yonedaEquiv_symm_comp]
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.cast (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) hp.symm
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast (c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)))
    (sliceIdentityCone_terminal (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) hp.symm
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialRestriction F c).app (Opposite.op ⦋0⦌) (initialValueCone hc F) = d :=
    Subtype.ext (initialValueCone_restriction hc F)
  rw [ht]
  exact hd

/-- 辺のホモトピー圏上で単体的射を作用させる。 -/
def coneHomotopyMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (q : X ⟶ Y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X).functor ⋙ (hoFunctor.map q).toFunctor ⋙
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge Y).inverse

/-- この作用は辺の像そのものを与える。 -/
theorem coneHomotopyMap_homMk {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    (coneHomotopyMap q).map (SSet.Truncated.HomotopyCategory₂.homMk e) =
      SSet.Truncated.HomotopyCategory₂.homMk (e.map ((truncation 2).map q)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory _).map
    ((SSet.Truncated.mapHomotopyCategory ((truncation 2).map q)).map
      (SSet.Truncated.HomotopyCategory.homMk e)) = _
  rw [SSet.Truncated.mapHomotopyCategory_homMk]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory, SSet.Truncated.HomotopyCategory.lift_map_homMk]

/-- 一単体が一致する辺の可逆性は、端点の表示によらない。 -/
theorem coneEdge_isIso_of_edge_eq {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (e' : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y')
    (h : e.edge = e'.edge) [IsIso (SSet.Truncated.HomotopyCategory₂.homMk e')] :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) := by
  have hs : x = x' := e.src_eq.symm.trans ((congrArg _ h).trans e'.src_eq)
  have ht : y = y' := e.tgt_eq.symm.trans ((congrArg _ h).trans e'.tgt_eq)
  subst x' y'
  have hh : e = e' := SSet.Truncated.Edge.ext h
  rw [hh]
  infer_instance

/-- 標準錐の始対象への脚は退化した恒等一単体である。 -/
theorem initialValueCone_leg {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (initialValueCone hc F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hc ≫ F)) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone_at_point, SSet.const_comp,
    SSet.comp_const]
  change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op _ =
    X.map (SimplexCategory.σ (0 : Fin 1)).op _
  exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ => X.map α.op (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) (by decide)

/-- 指定錐と始対象の値の標準錐との同型は h(sliceOver F) にある。 -/
def initialLimitConeIso {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) :
    (SSet.HomotopyCategory.mk a : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver F)) ≅
      SSet.HomotopyCategory.mk (initialValueCone hc F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso a (initialValueCone hc F) ha (initialValueCone_isLimit hc F)

/-- 極限錐の比較同型を表す slice の辺を選ぶ。 -/
def initialLimitConeEdge {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) :
    SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver F)) a (initialValueCone hc F) :=
  Classical.choose (SSet.Truncated.HomotopyCategory₂.homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso₂ ha (initialValueCone_isLimit hc F)).hom)

/-- 選んだ辺の類は、二次切断で計算した同じ比較同型である。 -/
theorem initialLimitConeEdge_homMk {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) :
    SSet.Truncated.HomotopyCategory₂.homMk (initialLimitConeEdge hc F a ha) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso₂ ha (initialValueCone_isLimit hc F)).hom :=
  Classical.choose_spec (SSet.Truncated.HomotopyCategory₂.homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso₂ ha (initialValueCone_isLimit hc F)).hom)

/-- slice の比較辺は、公開した h(sliceOver) の比較同型そのものを表す。 -/
theorem initialLimitConeEdge_path {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver F)).functor.map
        (SSet.Truncated.HomotopyCategory₂.homMk (initialLimitConeEdge hc F a ha)) =
      (initialLimitConeIso hc F a ha).hom := by
  rw [initialLimitConeEdge_homMk]
  rfl

/-- 比較同型の頂点への射影は、指定した各脚と三角形で両立する。 -/
theorem initialLimitConeEdge_leg {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) (t : (nerve I) _⦋0⦌) :
    SSet.Truncated.HomotopyCategory₂.homMk
        ((initialLimitConeEdge hc F a ha).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection F))) ≫
      SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (initialValueCone hc F) t) =
        SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg a t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg_homMk_comp (initialLimitConeEdge hc F a ha) t

/-- 極限錐の始対象への実際の脚は導来同値を表す。 -/
theorem initialLimitLeg_isIso {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) := by
  let e := initialLimitConeEdge hc F a ha
  have hi : IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) := by
    rw [initialLimitConeEdge_homMk]
    infer_instance
  have hi' : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection F)))) := by
    rw [← coneHomotopyMap_homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection F) e]
    infer_instance
  have hj : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (initialValueCone hc F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) := by
    have : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)))) := by
      rw [SSet.Truncated.HomotopyCategory₂.homMk_id]
      infer_instance
    exact coneEdge_isIso_of_edge_eq _ _ (initialValueCone_leg hc F)
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg_homMk_comp e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)]
  infer_instance

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end InitialLimit

/-! ## 指定された普遍 perfectoid 化と導来極限の比較（旧 PerfectoidizationInterface/InitialBridge.lean）

概要：任意に与えた普遍単位を、同じ宇宙の標的圏の始対象として使う。
方針：環の一意因子分解を始対象性へ移し、二宇宙版の cofinality で指定錐を比較する。
規約：普遍環の存在は仮定せず、指定された単位の普遍性だけを引数に取る。
使われ方：Π2-5 の錐・単位付き導来同値、離散性、H⁰ の環同型。
-/

@[expose] public noncomputable section InitialBridge

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ) [Fact p.Prime]

/-- 指定された普遍単位を、制限した標的圏の対象として保持する。 -/
def specifiedTarget (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) : PerfUnder_u p S :=
  ⟨Under.mk (CommRingCat.ofHom η), hC.1⟩

/-- 環の普遍性から得る、指定標的から任意の perfectoid 標的への射。 -/
def specifiedTargetTo (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) (T : PerfUnder_u p S) :
    specifiedTarget p S η hC ⟶ T :=
  ObjectProperty.homMk (Under.homMk
    (CommRingCat.ofHom (hC.2 T.obj.right T.property T.obj.hom.hom).choose)
    (CommRingCat.hom_ext (hC.2 T.obj.right T.property T.obj.hom.hom).choose_spec.1))

/-- 同じ Type u の全 perfectoid 標的に対する環の普遍性は、始対象性そのもの。 -/
def specifiedTarget_isInitial (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) : IsInitial (specifiedTarget p S η hC) := by
  letI (T : PerfUnder_u p S) : Unique (specifiedTarget p S η hC ⟶ T) :=
    { default := specifiedTargetTo p S η hC T
      uniq := fun f => by
        ext1
        ext1
        apply CommRingCat.hom_ext
        apply (hC.2 T.obj.right T.property T.obj.hom.hom).choose_spec.2
        exact congrArg (fun (g : S ⟶ T.obj.right) => g.hom) (Under.w f.hom) }
  exact IsInitial.ofUnique _

variable (R : Type u) [CommRing R]

/-- 指定された普遍環に、R → S を通した R 代数構造を与える。 -/
def specifiedAlgebra (S : A_R R) {C : Type u} [CommRing C]
    (ηC : S.right →+* C) (hC : IsPerfectoidization p ηC) : A_R R :=
  (targetAlgebra R p S).obj (specifiedTarget p S.right ηC hC)

/-- 図式の一頂点への脚を、界面の join の一単体の表記で評価する。 -/
theorem coneLeg_edge {K X : SSet.{u + 1}} {G : K ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone G) (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg a v).edge = a.val.app _ (joinLegSimplex v) := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm v) ≫ a.val) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp]
  congr 1
  rw [SSet.yonedaEquiv_comp]
  have h00 : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0 :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) Δ[0] ≅ Δ[1]).inv =
      joinLegSimplex (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1}))) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom.app (Opposite.op ⦋1⦌))).injective
    rw [← SSet.yonedaEquiv_comp, Iso.inv_hom_id]
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  rw [h00]
  simp [joinLegSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom]

section Interface
variable (hR : IsIntegralPerfectoid R p) (F : PerfectoidizationInterfaceE3 R p hR)
    (S : A_R R) {C : Type u} [CommRing C]
    (ηC : S.right →+* C) (hC : IsPerfectoidization p ηC)

/-- 比較は指定された界面の錐と始対象からの標準錐の間の h(sliceOver) の同型。 -/
def specifiedLimitConeIso :
    (SSet.HomotopyCategory.mk (F.limitCone S).cone :
        SSet.hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (targetDiagram R p S))) ≅
      SSet.HomotopyCategory.mk (initialValueCone
        (specifiedTarget_isInitial p S.right ηC hC) (targetDiagram R p S)) :=
  initialLimitConeIso (specifiedTarget_isInitial p S.right ηC hC)
    (targetDiagram R p S) (F.limitCone S).cone (F.limit_isLimit S)

/-- 指定錐の実際の射影は、指定普遍環への導来同値を表す。 -/
theorem specifiedProjection_isIso :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      ((F.limitCone S).projectionEdge (specifiedTarget p S.right ηC hC)).toTruncated) := by
  have := initialLimitLeg_isIso (specifiedTarget_isInitial p S.right ηC hC)
    (targetDiagram R p S) (F.limitCone S).cone (F.limit_isLimit S)
  apply coneEdge_isIso_of_edge_eq _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (F.limitCone S).cone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (specifiedTarget p S.right ηC hC)))
  change ((F.limitCone S).projectionEdge (specifiedTarget p S.right ηC hC)).edge = _
  exact ((F.limitCone S).projectionEdge_eq _).trans (coneLeg_edge _ _).symm

/-- vertex perfd S と指定された C の離散像の同型。射は元の錐の射影である。 -/
def specifiedDerivedIso :
    (⟨vertex R F.perfd S⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory R) ≅
      ⟨vertex R (J R) (specifiedAlgebra p R S ηC hC)⟩ := by
  have := specifiedProjection_isIso p R hR F S ηC hC
  exact asIso (SSet.Truncated.HomotopyCategory₂.homMk
    ((F.limitCone S).projectionEdge (specifiedTarget p S.right ηC hC)).toTruncated)

/-- 元の単位と比較同型の合成は、指定された S → C の離散像に一致する。 -/
theorem specifiedDerivedIso_unit :
    SSet.Truncated.HomotopyCategory₂.homMk (component R F.unit S).toTruncated ≫
        (specifiedDerivedIso p R hR F S ηC hC).hom =
      SSet.Truncated.HomotopyCategory₂.homMk
        (edge R (J R) (targetUnitMap R p S (specifiedTarget p S.right ηC hC))).toTruncated := by
  let T := specifiedTarget p S.right ηC hC
  let cc := F.limitCone S
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (cc.sourceCone.postcomp (J R)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T)).edge =
      (edge R (J R) (targetUnitMap R p S T)).edge := by
    rw [coneLeg_edge]
    change (J R).app _ (cc.sourceCone.val.app _ (joinLegSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T))) = _
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T = ComposableArrows.mk₀ T from rfl, cc.source_legs T]
    rfl
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg cc.cone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T)).edge = (cc.projectionEdge T).edge := by
    rw [coneLeg_edge, cc.projectionEdge_eq]
    rfl
  let raw := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLegCompStruct cc.overSource.toTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T)
  let triangle : SSet.Truncated.Edge.CompStruct (component R F.unit S).toTruncated
      (cc.projectionEdge T).toTruncated (edge R (J R) (targetUnitMap R p S T)).toTruncated :=
    ⟨raw.simplex, raw.d₂.trans cc.overSource_unit, raw.d₀.trans hp, raw.d₁.trans hs⟩
  exact triangle.homotopyCategory₂_fac

include ηC hC in
/-- 指定普遍環が存在すれば、導来 perfectoid 化全体は離散である。 -/
theorem specified_disc : Disc R (vertex R F.perfd S) := by
  have hJ : Disc R (vertex R (J R) (specifiedAlgebra p R S ηC hC)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleHeartVertex_disc ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).obj (specifiedAlgebra p R S ηC hC))
  intro i hi
  exact (hJ i hi).of_iso ((HFunctor R i).mapIso (specifiedDerivedIso p R hR F S ηC hC))

/-- 指定錐の H⁰ 射影は、底の線形写像が同型なので環の同型である。 -/
theorem specifiedRingProjection_isIso :
    IsIso ((F.limitCone S).projection (specifiedTarget p S.right ηC hC)).right := by
  have := specifiedProjection_isIso p R hR F S ηC hC
  have hmap : IsIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).map
      ((F.limitCone S).projection (specifiedTarget p S.right ηC hC))) := by
    rw [← (F.limitCone S).projection_compat]
    dsimp only [HMap]
    infer_instance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).map
    ((F.limitCone S).projection (specifiedTarget p S.right ηC hC)))

/-- H⁰ の環と指定普遍環の同型。射は指定錐の環準同型である。 -/
def specifiedRingIso : (F.h0.ringFunctor.obj S).right ≅ CommRingCat.of C := by
  have := specifiedRingProjection_isIso p R hR F S ηC hC
  exact asIso ((F.limitCone S).projection (specifiedTarget p S.right ηC hC)).right

/-- 環同型は元の二つの単位を保つ。 -/
theorem specifiedRingIso_unit :
    (specifiedRingIso p R hR F S ηC hC).hom.hom.comp (F.h0.unit.app S).right.hom = ηC :=
  congrArg (fun (f : S ⟶ specifiedAlgebra p R S ηC hC) => f.right.hom)
    ((F.limitCone S).projection_unit (specifiedTarget p S.right ηC hC))

end Interface

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end InitialBridge

/-! ## 界面を引数とする整代数の perfectoid 化の存在（旧 PerfectoidizationInterface/IntegralExistence.lean）

概要：integral 欄の離散性に、離散時の環の普遍性を適用する。
方針：指定された H⁰ の環と指定単位をそのまま存在の証人に取る。
規約：既存の存在入力を使用せず、S の完備性や有限性を仮定しない。
使われ方：Π2-6 の界面依存版。旧 Inputs の置換は別工程。
-/

@[expose] public section IntegralExistence

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface

/-- 整代数の普遍 perfectoid 化は、E3 の integral と universal の欄から従う
（BS 著者版 Theorem 10.11 と Corollary 8.14 の環としての帰結、序論の Theorem 1.17 (1)）。 -/
theorem exists_perfectoidization_of_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (F : PerfectoidizationInterfaceE3 R p hR) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f := by
  have hInt : (letI : Algebra R (ofAlgebra R S).right := (ofAlgebra R S).hom.hom.toAlgebra
      Algebra.IsIntegral R (ofAlgebra R S).right) := by
    change @Algebra.IsIntegral R S _ _ (algebraMap R S).toAlgebra
    rw [toAlgebra_algebraMap]
    infer_instance
  exact ⟨(F.h0.ringFunctor.obj (ofAlgebra R S)).right, inferInstance,
    (F.h0.unit.app (ofAlgebra R S)).right.hom,
    F.universal (ofAlgebra R S) (F.integral (ofAlgebra R S) hInt).1⟩

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end IntegralExistence

/-! ## 整代数の普遍 perfectoid 化（界面から導出した定理）（旧 PerfectoidizationInterface/IntegralPerfectoidization.lean）

従来 BS 著者版 Theorem 1.17(1) を直接引用していた公開入口である。
現在は導来 perfectoid 化界面の存在だけを引用し、integral と universal から導く。
公開名・型と、非完備を含む任意の整代数という範囲を保つ。
-/

public section IntegralPerfectoidization

namespace SerrePositivity.BhattScholze.Inputs

/--
## 概要
BS 著者版 Theorem 1.17(1) の存在命題を、E3 界面から導出した定理。

## 方針
界面の存在を取り出し、Π2-6 の integral → 離散性 → universal の証明へ渡す。
integral の原典は BS 著者版 Theorem 10.11、離散時 universal の原典は BS 著者版 Corollary 8.14 である。

## 規約
この公開入口は以前 BS 著者版 Theorem 1.17(1) の文献入力であったが、現在は直接の未証明箇所を持たない。
有限性・有限表示性・有界 p 冪ねじれ・S の完備性は追加しない。
原典：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf 。

## 使われ方
既存の同じ公開名・型で整代数の普遍 perfectoid 化を供給する。
-/
theorem exists_perfectoidization_of_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f := by
  exact PerfectoidizationInterface.exists_perfectoidization_of_integral R S p hR
    (Classical.choice (exists_perfectoidizationInterfaceE3 R p hR))

end SerrePositivity.BhattScholze.Inputs

end IntegralPerfectoidization

/-! ## 整代数の原典入力から有限版と完備化版への接続（旧 PerfectoidizationInterface/FiniteIntegralExistence.lean）

有限代数の整性を確認して原典の普遍 perfectoid 化を適用する。
完備化の場合には、同じ目標環と写像の一意延長を用いて普遍性を移す。
新しい対象を選び直さず、古典完備化と導来完備化の同値も仮定しない。
-/

@[expose] public section FiniteIntegralExistence

namespace SerrePositivity.BhattScholze

/-- 有限代数の存在主張は、整代数についての原典の存在入力への適用である。
有限表示性はこの導出には不要である。 -/
theorem exists_perfectoidization_of_finite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f :=
  Inputs.exists_perfectoidization_of_integral R S p hR

/-- 整代数の古典 p 進完備化にも、同じ環を使って普遍 perfectoid 化を与えられる。
元環の普遍性と完備化への一意延長からの系であり、prismatic perfection 本体の定義ではない。 -/
theorem exists_perfectoidization_of_completed_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C)
      (f : AdicCompletion (Ideal.span {(p : S)}) S →+* C), IsPerfectoidization p f := by
  obtain ⟨C, hC, f, hf⟩ := Inputs.exists_perfectoidization_of_integral R S p hR
  exact ⟨C, hC, hf.completionMap p, hf.to_completion p⟩

end SerrePositivity.BhattScholze

end FiniteIntegralExistence
