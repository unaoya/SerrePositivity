module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEdgeCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.HornPointJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge

/-!
# 始対象の値から指定極限錐を計算する

一般の∞圏の共終性を使い、指定された始対象から極限錐を計算する。
-/

universe u v w

/-! ## 始対象の値による指定極限錐の計算

概要：二宇宙の cofinality を使い、始対象からの標準錐を極限錐にする。
方針：一点図式の恒等錐の終対象性を外側ホーンで検証し、制限で反映する。
規約：極限の比較は h(sliceOver) に保持する。
使われ方：普遍単位と指定錐の比較 の指定 perfectoid 化との比較。
-/

@[expose] public noncomputable section InitialLimit

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- 一点図式の恒等錐は slice の終対象である。 -/
theorem _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceIdentityCone_terminal {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌) :
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
def _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hc ≫ F, by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone_inr, Category.id_comp]⟩

/-- 始対象で制限した標準錐の射は定数射。 -/
theorem _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone_restriction {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialRestriction F c).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone hc F)).val =
      SSet.const (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hc ≫ F) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone_at_point, SSet.const_comp]

/-- 二宇宙版の cofinality により始対象の値の標準錐が極限になる。 -/
theorem _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone_isLimit {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone hc F) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialCofinality hc F
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialRestriction F c)
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c ≫ F = SSet.yonedaEquiv.symm (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint, SSet.yonedaEquiv_symm_comp]
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.cast (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) hp.symm
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast (c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceIdentityCone_terminal (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) hp.symm
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialRestriction F c).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone hc F) = d :=
    Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone_restriction hc F)
  rw [ht]
  exact hd

/-- 辺のホモトピー圏上で単体的射を作用させる。 -/
def _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.coneHomotopyMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (q : X ⟶ Y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X).functor ⋙ (hoFunctor.map q).toFunctor ⋙
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge Y).inverse

/-- この作用は辺の像そのものを与える。 -/
theorem _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.coneHomotopyMap_homMk {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.coneHomotopyMap q).map (SSet.Truncated.HomotopyCategory₂.homMk e) =
      SSet.Truncated.HomotopyCategory₂.homMk (e.map ((truncation 2).map q)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory _).map
    ((SSet.Truncated.mapHomotopyCategory ((truncation 2).map q)).map
      (SSet.Truncated.HomotopyCategory.homMk e)) = _
  rw [SSet.Truncated.mapHomotopyCategory_homMk]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory, SSet.Truncated.HomotopyCategory.lift_map_homMk]

/-- 一単体が一致する辺の可逆性は、端点の表示によらない。 -/
theorem _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.coneEdge_isIso_of_edge_eq {X : SSet.{u}} [Quasicategory X]
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
theorem _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone_leg {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone hc F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hc ≫ F)) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone_at_point, SSet.const_comp,
    SSet.comp_const]
  change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op _ =
    X.map (SimplexCategory.σ (0 : Fin 1)).op _
  exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ => X.map α.op (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) (by decide)

/-- 指定錐と始対象の値の標準錐との同型は h(sliceOver F) にある。 -/
def _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeIso {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) :
    (SSet.HomotopyCategory.mk a : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver F)) ≅
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone hc F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso a (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone hc F) ha (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone_isLimit hc F)

/-- 極限錐の比較同型を表す slice の辺を選ぶ。 -/
def _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) :
    SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver F)) a (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone hc F) :=
  Classical.choose (SSet.Truncated.HomotopyCategory₂.homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso₂ ha (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone_isLimit hc F)).hom)

/-- 選んだ辺の類は、二次切断で計算した同じ比較同型である。 -/
theorem _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge_homMk {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) :
    SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge hc F a ha) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso₂ ha (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone_isLimit hc F)).hom :=
  Classical.choose_spec (SSet.Truncated.HomotopyCategory₂.homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso₂ ha (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone_isLimit hc F)).hom)

/-- slice の比較辺は、公開した h(sliceOver) の比較同型そのものを表す。 -/
theorem _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge_path {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver F)).functor.map
        (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge hc F a ha)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeIso hc F a ha).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge_homMk]
  rfl

/-- 比較同型の頂点への射影は、指定した各脚と三角形で両立する。 -/
theorem _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge_leg {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) (t : (nerve I) _⦋0⦌) :
    SSet.Truncated.HomotopyCategory₂.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge hc F a ha).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection F))) ≫
      SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone hc F) t) =
        SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg a t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg_homMk_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge hc F a ha) t

/-- 極限錐の始対象への実際の脚は導来同値を表す。 -/
theorem _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitLeg_isIso {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge hc F a ha
  have hi : IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialLimitConeEdge_homMk]
    infer_instance
  have hi' : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection F)))) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.coneHomotopyMap_homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection F) e]
    infer_instance
  have hj : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone hc F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) := by
    have : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)))) := by
      rw [SSet.Truncated.HomotopyCategory₂.homMk_id]
      infer_instance
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.coneEdge_isIso_of_edge_eq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialValueCone_leg hc F)
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg_homMk_comp e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)]
  infer_instance

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end InitialLimit

/-! ## 指定された普遍 perfectoid 化と導来極限の比較

概要：任意に与えた普遍単位を、同じ宇宙の標的圏の始対象として使う。
方針：環の一意因子分解を始対象性へ移し、二宇宙版の cofinality で指定錐を比較する。
規約：普遍環の存在は仮定せず、指定された単位の普遍性だけを引数に取る。
使われ方：普遍単位と指定錐の比較 の錐・単位付き導来同値、離散性、H⁰ の環同型。
-/

