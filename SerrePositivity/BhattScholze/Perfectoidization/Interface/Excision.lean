module

public import SerrePositivity.BhattScholze.Perfectoidization.Interface.Derived
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FiberLongExactSequence
public import SerrePositivity.CommutativeAlgebra.DerivedSingleTrianglePullback
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.BhattScholze.Perfectoidization.Interface.IntegralExistence
public import SerrePositivity.BhattScholze.Inputs.PerfectoidizationInterface
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# 導来 perfectoid 化の界面から環としての excision へ（BS 著者版 Corollary 8.12 の環版）

## 概要
離散性を仮定した excision の橋、四つの指定普遍環からの excision、環としての excision の引き戻し四角形。

## 方針
四頂点の離散性とファイバー列の長完全列から環の引き戻しを得る。差写像の全射性は界面から証明する。

## 規約
導来 perfectoid 化の界面の存在を引用する。

## 使われ方
perfectoid 化の excision の適用（Perfectoidization/Excision）、CLMST。
-/

universe u

/-! ## 離散性を仮定した perfectoid 化の excision の橋

概要：界面の引き戻しを指定四辺の長完全列に送り、環の引き戻しと差の全射性を得る。
方針：ホモトピー引き戻しの長完全列 の零次の列を H⁰ の環構造の比較同型で移す。
規約：四頂点の Disc は仮定として受け取り、始対象による離散性の導出は保留する。
使われ方：環の excision の比較。旧 Inputs の excision と存在入力には依存しない。
-/

@[expose] public noncomputable section ExcisionBridge

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) [CommRing R]

/-- 長完全列の両端の消滅から零次の中央三項が短完全になる。 -/
theorem squareHZero_shortExact
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F)
    (hD : IsZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology R (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)))
    (hA : IsZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology R 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomology₂ F hF 0).ShortExact := by
  obtain ⟨h₁, h₂, h₃⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyLongExact F hF 0
  have hm := h₁.mono_g (hD.eq_of_src _ _)
  have he := h₃.epi_f (hA.eq_of_tgt _ _)
  exact { exact := h₂, mono_f := hm, epi_g := he }

section Square
variable {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d)
    (P : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)

private lemma ordinarySquare_bottom :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomEdge ≫ ordinarySquare R a b c d w =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ a) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTriangle_bottom, Category.assoc, ordinarySquare_triangle_one]
  apply SSet.yonedaEquiv.injective
  exact CategoryTheory.nerve.δ₂_mk₂_eq a c

private lemma ordinarySquare_left :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftEdge ≫ ordinarySquare R a b c d w =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ b) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTriangle_left, Category.assoc, ordinarySquare_triangle_zero]
  apply SSet.yonedaEquiv.injective
  exact CategoryTheory.nerve.δ₂_mk₂_eq b d

private lemma ordinarySquare_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ ordinarySquare R a b c d w =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ c) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge, Category.assoc, ordinarySquare_triangle_one]
  apply SSet.yonedaEquiv.injective
  exact CategoryTheory.nerve.δ₀_mk₂_eq a c

private lemma ordinarySquare_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ ordinarySquare R a b c d w =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ d) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge, Category.assoc, ordinarySquare_triangle_zero]
  apply SSet.yonedaEquiv.injective
  exact CategoryTheory.nerve.δ₀_mk₂_eq b d

private lemma square_bottom_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomDgEdge (ordinarySquare R a b c d w ≫ P)).edge =
      (edge R P a).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomDgEdge_edge, ← Category.assoc, _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ordinarySquare_bottom]
  rw [SSet.yonedaEquiv_comp]
  rfl

private lemma square_left_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftDgEdge (ordinarySquare R a b c d w ≫ P)).edge =
      (edge R P b).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftDgEdge_edge, ← Category.assoc, _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ordinarySquare_left]
  rw [SSet.yonedaEquiv_comp]
  rfl

private lemma square_right_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareRightDgEdge (ordinarySquare R a b c d w ≫ P)).edge =
      (edge R P c).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareRightDgEdge_edge, ← Category.assoc, _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ordinarySquare_right]
  rw [SSet.yonedaEquiv_comp]
  rfl

private lemma square_top_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareUpperDgEdge (ordinarySquare R a b c d w ≫ P)).edge =
      (edge R P d).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareUpperDgEdge_edge, ← Category.assoc, _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ordinarySquare_top]
  rw [SSet.yonedaEquiv_comp]
  rfl

private lemma edge_source_eq {x y x' y' : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌}
    (e : ((SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)).Edge x y)
    (e' : ((SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)).Edge x' y')
    (h : e.edge = e'.edge) : x = x' :=
  e.src_eq.symm.trans ((congrArg _ h).trans e'.src_eq)

private lemma edge_target_eq {x y x' y' : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌}
    (e : ((SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)).Edge x y)
    (e' : ((SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)).Edge x' y')
    (h : e.edge = e'.edge) : y = y' :=
  e.tgt_eq.symm.trans ((congrArg _ h).trans e'.tgt_eq)

private lemma square_A :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (ordinarySquare R a b c d w ≫ P)).vertex = vertex R P A :=
  _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.edge_source_eq R _ _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_bottom_edge R a b c d w P)

private lemma square_B :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBVertex (ordinarySquare R a b c d w ≫ P) = vertex R P B :=
  _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.edge_target_eq R _ _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_bottom_edge R a b c d w P)

private lemma square_C :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareCVertex (ordinarySquare R a b c d w ≫ P) = vertex R P C :=
  _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.edge_target_eq R _ _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_left_edge R a b c d w P)

private lemma square_D :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex (ordinarySquare R a b c d w ≫ P) = vertex R P D :=
  _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.edge_target_eq R _ _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_right_edge R a b c d w P)

end Square

/-- under 圏の指定構造射から R 代数構造を読む。 -/
abbrev underAlgebra (S : A_R R) : Algebra R S.right := S.hom.hom.toAlgebra
section UnderAlgebra
attribute [local instance] underAlgebra

/-- under 圏の射を、同じ環準同型の R 代数射にする。 -/
def underAlgHom {S T : A_R R} (f : S ⟶ T) : S.right →ₐ[R] T.right :=
  { f.right.hom with
    commutes' := fun r => congrArg (fun (g : CommRingCat.of R ⟶ T.right) => g.hom r)
      (Under.w f) }

end UnderAlgebra

section HZeroSquare
attribute [local instance] underAlgebra
variable {P : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R}
    {η : NatInfinity R (J R) P} (h0 : H0RingData R P η)
    {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d)

private def ringModuleIso (S : A_R R) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌)
    (hx : x = vertex R P S) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).obj (h0.ringFunctor.obj S) ≅ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology R 0 x :=
  h0.moduleIso S ≪≫ eqToIso (congrArg (H R 0) hx.symm)

private lemma ringModuleIso_map {S T : A_R R} (f : S ⟶ T)
    {x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌}
    (hx : x = vertex R P S) (hy : y = vertex R P T)
    (e : ((SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R)).Edge x y)
    (he : e.edge = (edge R P f).edge) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).map (h0.ringFunctor.map f) ≫
        (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso R h0 T y hy).hom =
      (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso R h0 S x hx).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyMap R 0 e := by
  subst x y
  have he' : e = (edge R P f).toTruncated := SSet.Truncated.Edge.ext he
  subst e
  simpa only [_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso, eqToIso_refl, Iso.trans_refl, HMap, HFunctor,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyFunctor] using h0.map_compat f

/-- H⁰ の環の四辺を、元の商図式の順序で持つ短複体。 -/
def h0SquareShortComplex : ShortComplex (ModuleCat.{u} R) :=
  algHomPullbackShortComplex
    (underAlgHom R (h0.ringFunctor.map a)) (underAlgHom R (h0.ringFunctor.map b))
    (underAlgHom R (h0.ringFunctor.map c)) (underAlgHom R (h0.ringFunctor.map d)) (by
      apply AlgHom.ext
      intro x
      exact congrArg (fun (f : h0.ringFunctor.obj A ⟶ h0.ringFunctor.obj D) =>
        f.right.hom x) ((h0.ringFunctor.map_comp a c).symm.trans
          ((congrArg h0.ringFunctor.map w).trans (h0.ringFunctor.map_comp b d))))

set_option maxHeartbeats 800000 in
-- 四辺・直和・導来比較の同時正規化に必要。
private def h0SquareSequenceIso
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (ordinarySquare R a b c d w ≫ P)) :
    h0SquareShortComplex R h0 a b c d w ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomology₂ (ordinarySquare R a b c d w ≫ P) hF 0 := by
  let eA := _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso R h0 A _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_A R a b c d w P)
  let eB := _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso R h0 B _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_B R a b c d w P)
  let eC := _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso R h0 C _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_C R a b c d w P)
  let eD := _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso R h0 D _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_D R a b c d w P)
  let eBC := (ModuleCat.biprodIsoProd
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).obj (h0.ringFunctor.obj B))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule R).obj (h0.ringFunctor.obj C))).symm ≪≫ biprod.mapIso eB eC
  refine ShortComplex.isoMk eA eBC eD ?_ ?_
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomology₂_f]
    apply biprod.hom_ext
    · simp only [eBC, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom,
        Category.assoc, biprod.map_fst,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyPair, biprod.lift_fst]
      rw [← Category.assoc _ biprod.fst eB.hom,
        ModuleCat.biprodIsoProd_inv_comp_fst]
      exact (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso_map R h0 a (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_A R a b c d w P)
        (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_B R a b c d w P) _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_bottom_edge R a b c d w P)).symm
    · simp only [eBC, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom,
        Category.assoc, biprod.map_snd,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyPair, biprod.lift_snd]
      rw [← Category.assoc _ biprod.snd eC.hom,
        ModuleCat.biprodIsoProd_inv_comp_snd]
      exact (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso_map R h0 b (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_A R a b c d w P)
        (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_C R a b c d w P) _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_left_edge R a b c d w P)).symm
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomology₂_g]
    have hc := _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso_map R h0 c (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_B R a b c d w P)
      (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_D R a b c d w P) _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_right_edge R a b c d w P)
    have hd := _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.ringModuleIso_map R h0 d (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_C R a b c d w P)
      (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_D R a b c d w P) _ (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_top_edge R a b c d w P)
    have hdiff : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyDifference (ordinarySquare R a b c d w ≫ P) 0 =
        biprod.fst ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyMap R 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareRightDgEdge
          (ordinarySquare R a b c d w ≫ P)) -
        biprod.snd ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyMap R 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareUpperDgEdge
          (ordinarySquare R a b c d w ≫ P)) := by
      apply biprod.hom_ext' <;> simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyDifference]
    simp only [eBC, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, hdiff,
      Preadditive.comp_sub, Category.assoc]
    simp only [biprod.map_fst_assoc, biprod.map_snd_assoc]
    rw [← hc, ← hd]
    simp only [← Category.assoc,
      ModuleCat.biprodIsoProd_inv_comp_fst, ModuleCat.biprodIsoProd_inv_comp_snd,
      ← Preadditive.sub_comp]
    congr 1

/-- H⁰ の環の対・差の列は、導来引き戻しと端点の離散性から短完全になる。 -/
theorem h0SquareShortComplex_shortExact
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (ordinarySquare R a b c d w ≫ P))
    (hA : Disc R (vertex R P A)) (hD : Disc R (vertex R P D)) :
    (h0SquareShortComplex R h0 a b c d w).ShortExact := by
  have hzD : IsZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology R (-1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex (ordinarySquare R a b c d w ≫ P))) := by
    rw [_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_D R a b c d w P]
    exact hD (-1) (by decide)
  have hzA : IsZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology R 1
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (ordinarySquare R a b c d w ≫ P)).vertex) := by
    rw [_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.square_A R a b c d w P]
    exact hA 1 (by decide)
  exact ShortComplex.shortExact_of_iso (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.h0SquareSequenceIso R h0 a b c d w hF).symm
    (squareHZero_shortExact R _ hF hzD hzA)

/-- 元の四辺の H⁰ の環準同型は環の引き戻しをなす。 -/
theorem h0Square_isPullback
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (ordinarySquare R a b c d w ≫ P))
    (hA : Disc R (vertex R P A)) (hD : Disc R (vertex R P D)) :
    IsPullback (h0.ringFunctor.map a).right (h0.ringFunctor.map b).right
      (h0.ringFunctor.map c).right (h0.ringFunctor.map d).right :=
  algHom_isPullback_of_module_shortExact _ _ _ _ _
    (h0SquareShortComplex_shortExact R h0 a b c d w hF hA hD)

/-- 差は加法的な写像として全射であり、各環準同型の全射性は要求しない。 -/
theorem h0Square_difference_surjective
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (ordinarySquare R a b c d w ≫ P))
    (hA : Disc R (vertex R P A)) (hD : Disc R (vertex R P D)) :
    Function.Surjective (fun x : (h0.ringFunctor.obj B).right × (h0.ringFunctor.obj C).right =>
      (h0.ringFunctor.map c).right.hom x.1 - (h0.ringFunctor.map d).right.hom x.2) := by
  exact (ModuleCat.epi_iff_surjective _).mp
    (h0SquareShortComplex_shortExact R h0 a b c d w hF hA hD).epi_g

end HZeroSquare

section SpecifiedTargets
variable (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (F : PerfectoidizationInterfaceE3 R p hR)

/-- 離散時の環の普遍性だけで、H⁰ 環と指定された普遍環を比較する。 -/
def h0PerfectoidEquiv (S : A_R R) (hS : Disc R (vertex R F.perfd S))
    {C : Type u} [CommRing C] (ηC : S.right →+* C) (hC : IsPerfectoidization p ηC) :
    (F.h0.ringFunctor.obj S).right ≃+* C :=
  Classical.choose ((F.universal S hS).exists_equiv p hC)

/-- 比較環同型は元の二つの単位を保つ。 -/
theorem h0PerfectoidEquiv_unit (S : A_R R) (hS : Disc R (vertex R F.perfd S))
    {C : Type u} [CommRing C] (ηC : S.right →+* C) (hC : IsPerfectoidization p ηC) :
    (h0PerfectoidEquiv R p hR F S hS ηC hC).toRingHom.comp (F.h0.unit.app S).right.hom = ηC :=
  Classical.choose_spec ((F.universal S hS).exists_equiv p hC)

/-- H⁰ の元の辺は、比較同型のもとで指定された普遍環の誘導射に一致する。 -/
theorem h0PerfectoidEquiv_naturality {S T : A_R R} (f : S ⟶ T)
    (hS : Disc R (vertex R F.perfd S)) (hT : Disc R (vertex R F.perfd T))
    {C D : Type u} [CommRing C] [CommRing D]
    (ηC : S.right →+* C) (ηD : T.right →+* D)
    (hC : IsPerfectoidization p ηC) (hD : IsPerfectoidization p ηD) :
    (h0PerfectoidEquiv R p hR F T hT ηD hD).toRingHom.comp
        (F.h0.ringFunctor.map f).right.hom =
      (IsPerfectoidization.map hC hD f.right.hom).comp
        (h0PerfectoidEquiv R p hR F S hS ηC hC).toRingHom := by
  have hnat : (F.h0.ringFunctor.map f).right.hom.comp (F.h0.unit.app S).right.hom =
      (F.h0.unit.app T).right.hom.comp f.right.hom :=
    congrArg (fun (g : S ⟶ F.h0.ringFunctor.obj T) => g.right.hom)
      (F.h0.unit.naturality f).symm
  apply ((F.universal S hS).lift_unique hD.1 (ηD.comp f.right.hom) _ ?_).trans
    (((F.universal S hS).lift_unique hD.1 (ηD.comp f.right.hom) _ ?_).symm)
  · rw [RingHom.comp_assoc, hnat, ← RingHom.comp_assoc, h0PerfectoidEquiv_unit]
  · rw [RingHom.comp_assoc, h0PerfectoidEquiv_unit, IsPerfectoidization.map_comp]

/-- 四つの離散性を受け取り、指定された普遍環の四辺へ短完全列の帰結を移す。 -/
theorem specifiedSquare_of_disc
    {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (ordinarySquare R a b c d w ≫ F.perfd))
    (hA : Disc R (vertex R F.perfd A)) (hB : Disc R (vertex R F.perfd B))
    (hC : Disc R (vertex R F.perfd C)) (hD : Disc R (vertex R F.perfd D))
    {A' B' C' D' : Type u} [CommRing A'] [CommRing B'] [CommRing C'] [CommRing D']
    {ηA : A.right →+* A'} {ηB : B.right →+* B'}
    {ηC : C.right →+* C'} {ηD : D.right →+* D'}
    (hA' : IsPerfectoidization p ηA) (hB' : IsPerfectoidization p ηB)
    (hC' : IsPerfectoidization p ηC) (hD' : IsPerfectoidization p ηD) :
    let a' := IsPerfectoidization.map hA' hB' a.right.hom
    let b' := IsPerfectoidization.map hA' hC' b.right.hom
    let c' := IsPerfectoidization.map hB' hD' c.right.hom
    let d' := IsPerfectoidization.map hC' hD' d.right.hom
    IsPullback (CommRingCat.ofHom a') (CommRingCat.ofHom b')
        (CommRingCat.ofHom c') (CommRingCat.ofHom d') ∧
      Function.Surjective (fun x : B' × C' => c' x.1 - d' x.2) := by
  let eA := h0PerfectoidEquiv R p hR F A hA ηA hA'
  let eB := h0PerfectoidEquiv R p hR F B hB ηB hB'
  let eC := h0PerfectoidEquiv R p hR F C hC ηC hC'
  let eD := h0PerfectoidEquiv R p hR F D hD ηD hD'
  have ha := h0PerfectoidEquiv_naturality R p hR F a hA hB ηA ηB hA' hB'
  have hb := h0PerfectoidEquiv_naturality R p hR F b hA hC ηA ηC hA' hC'
  have hc := h0PerfectoidEquiv_naturality R p hR F c hB hD ηB ηD hB' hD'
  have hd := h0PerfectoidEquiv_naturality R p hR F d hC hD ηC ηD hC' hD'
  constructor
  · exact (h0Square_isPullback R F.h0 a b c d w hF hA hD).of_iso
      eA.toCommRingCatIso eB.toCommRingCatIso eC.toCommRingCatIso eD.toCommRingCatIso
      (CommRingCat.hom_ext ha) (CommRingCat.hom_ext hb)
      (CommRingCat.hom_ext hc) (CommRingCat.hom_ext hd)
  · intro z
    obtain ⟨x, hx⟩ := h0Square_difference_surjective R F.h0 a b c d w hF hA hD (eD.symm z)
    refine ⟨(eB x.1, eC x.2), ?_⟩
    change IsPerfectoidization.map hB' hD' c.right.hom (eB x.1) -
      IsPerfectoidization.map hC' hD' d.right.hom (eC x.2) = z
    have hcx : eD ((F.h0.ringFunctor.map c).right.hom x.1) =
        IsPerfectoidization.map hB' hD' c.right.hom (eB x.1) := RingHom.congr_fun hc x.1
    have hdx : eD ((F.h0.ringFunctor.map d).right.hom x.2) =
        IsPerfectoidization.map hC' hD' d.right.hom (eC x.2) := RingHom.congr_fun hd x.2
    rw [← hcx, ← hdx]
    change eD ((F.h0.ringFunctor.map c).right.hom x.1) -
      eD ((F.h0.ringFunctor.map d).right.hom x.2) = z
    dsimp only at hx
    rw [← map_sub, hx, eD.apply_symm_apply]

/-- 界面の excision と四頂点の Disc から、既存入力の四辺と差の全射性を得る。 -/
theorem excision_of_disc {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S.right (p : S.right)
      (ModuleCat.of S.right S.right))
    (hT : SerrePositivity.DerivedCompletion.IsModuleComplete T.right (p : T.right)
      (ModuleCat.of T.right T.right))
    (hI : SerrePositivity.DerivedCompletion.IsModuleComplete S.right (p : S.right)
      (ModuleCat.of S.right I)) (harc : ArcOutside R p f I)
    (dS : Disc R (vertex R F.perfd S)) (dT : Disc R (vertex R F.perfd T))
    (dQ : Disc R (vertex R F.perfd (quotientAlgebra R S I)))
    (dE : Disc R (vertex R F.perfd (quotientAlgebra R T (I.map f.right.hom))))
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S.right →+* C} {ηT : T.right →+* D}
    {ηQ : S.right ⧸ I →+* Q} {ηE : T.right ⧸ I.map f.right.hom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE) :
    let a := IsPerfectoidization.map hC hD f.right.hom
    let b := IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)
    let c := IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.right.hom))
    let d := IsPerfectoidization.map hQ hE
      (Ideal.quotientMap (I.map f.right.hom) f.right.hom Ideal.le_comap_map)
    IsPullback (CommRingCat.ofHom a) (CommRingCat.ofHom b)
        (CommRingCat.ofHom c) (CommRingCat.ofHom d) ∧
      Function.Surjective (fun x : D × Q => c x.1 - d x.2) :=
  specifiedSquare_of_disc R p hR F f (quotientProjection R S I)
    (quotientProjection R T (I.map f.right.hom)) (quotientComparison R f I)
    (quotientSquare_commutes R f I) (F.excision f I hS hT hI harc)
    dS dT dQ dE hC hD hQ hE

end SpecifiedTargets

set_option maxHeartbeats 800000 in
-- under 圏の四頂点と元の代数構造の同時照合に必要。
/-- 通常の R 代数を受け取る、旧 excision 入力の界面依存版と差の全射性。 -/
theorem perfectoidization_excision_of_disc
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (F : PerfectoidizationInterfaceE3 R p hR) (f : S →ₐ[R] T) (I : Ideal S)
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hT : SerrePositivity.DerivedCompletion.IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hI : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S I))
    (harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
      ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
      ∀ k : S →+* V, ¬ (I ≤ RingHom.ker k) →
        ∃! l : T →+* V, l.comp f.toRingHom = k)
    (dS : Disc R (vertex R F.perfd (ofAlgebra R S)))
    (dT : Disc R (vertex R F.perfd (ofAlgebra R T)))
    (dQ : Disc R (vertex R F.perfd (quotientAlgebra R (ofAlgebra R S) I)))
    (dE : Disc R (vertex R F.perfd (quotientAlgebra R (ofAlgebra R T) (I.map f.toRingHom))))
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S →+* C} {ηT : T →+* D}
    {ηQ : S ⧸ I →+* Q} {ηE : T ⧸ I.map f.toRingHom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE) :
    let a := IsPerfectoidization.map hC hD f.toRingHom
    let b := IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)
    let c := IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))
    let d := IsPerfectoidization.map hQ hE
      (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map)
    IsPullback (CommRingCat.ofHom a) (CommRingCat.ofHom b)
        (CommRingCat.ofHom c) (CommRingCat.ofHom d) ∧
      Function.Surjective (fun x : D × Q => c x.1 - d x.2) := by
  let f' : ofAlgebra R S ⟶ ofAlgebra R T :=
    Under.homMk (CommRingCat.ofHom f.toRingHom) (by
      ext r
      exact f.commutes r)
  exact excision_of_disc R p hR F f' I hS hT hI harc dS dT dQ dE hC hD hQ hE

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end ExcisionBridge

/-! ## 四つの指定普遍環からの excision

概要：界面と四つの IsPerfectoidization から、環の引き戻しと差の全射性を得る。
方針：指定錐を始対象で計算した離散性を、Disc 仮定付きの橋へ合成する。
規約：旧文献入力には依存せず、界面の存在も宣言しない。
使われ方：指定普遍環から環の excision を導く。
-/

@[expose] public noncomputable section Excision

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (F : PerfectoidizationInterfaceE3 R p hR)
    (f : S →ₐ[R] T) (I : Ideal S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hI : IsModuleComplete S (p : S) (ModuleCat.of S I))
    (harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
      ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
      ∀ k : S →+* V, ¬ (I ≤ RingHom.ker k) →
        ∃! l : T →+* V, l.comp f.toRingHom = k)
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S →+* C} {ηT : T →+* D}
    {ηQ : S ⧸ I →+* Q} {ηE : T ⧸ I.map f.toRingHom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE)

include F hS hT hI harc in
/-- 指定普遍環だけから、元の四辺の引き戻しと差写像の全射性を得る。 -/
theorem perfectoidization_excision :
    let a := IsPerfectoidization.map hC hD f.toRingHom
    let b := IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)
    let c := IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))
    let d := IsPerfectoidization.map hQ hE
      (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map)
    IsPullback (CommRingCat.ofHom a) (CommRingCat.ofHom b)
        (CommRingCat.ofHom c) (CommRingCat.ofHom d) ∧
      Function.Surjective (fun x : D × Q => c x.1 - d x.2) :=
  perfectoidization_excision_of_disc R S T p hR F f I hS hT hI harc
    (specified_disc p R hR F (ofAlgebra R S) ηS hC)
    (specified_disc p R hR F (ofAlgebra R T) ηT hD)
    (specified_disc p R hR F (quotientAlgebra R (ofAlgebra R S) I) ηQ hQ)
    (specified_disc p R hR F
      (quotientAlgebra R (ofAlgebra R T) (I.map f.toRingHom)) ηE hE) hC hD hQ hE

include F hS hT hI harc in
/-- 旧 excision 入力と同じ結論。追加引数は 導来 perfectoid 化の界面のみである。 -/
theorem perfectoidization_excision_isPullback :
    IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hC hD f.toRingHom))
      (CommRingCat.ofHom (IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)))
      (CommRingCat.ofHom (IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))))
      (CommRingCat.ofHom (IsPerfectoidization.map hQ hE
        (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map))) :=
  (perfectoidization_excision R S T p hR F f I hS hT hI harc hC hD hQ hE).1

include F hS hT hI harc hC in
/-- 同じ指定四辺の右辺 − 下辺は、加法的な差写像として全射である。 -/
theorem perfectoidization_excision_difference_surjective :
    Function.Surjective (fun x : D × Q =>
      IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom)) x.1 -
      IsPerfectoidization.map hQ hE
        (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map) x.2) :=
  (perfectoidization_excision R S T p hR F f I hS hT hI harc hC hD hQ hE).2

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end Excision

/-! ## perfectoid 化の環としての excision（界面から導出した定理）

従来 BS 著者版 Corollary 8.12 の環としての帰結を直接引用していた公開入口である。
現在は 導来 perfectoid 化の界面から指定錐の比較・離散性・長完全列を経て導く。
公開名・型と四つの指定普遍環・標準誘導射を保つので、CLMST の利用箇所は変更しない。
-/

public section ArcExcision

namespace SerrePositivity.BhattScholze.Inputs
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion

/--
## 概要
arc 条件を満たす商の四角形について、指定した普遍 perfectoid 化の環の四角形が引き戻しになる（BS 著者版 Corollary 8.12 の離散な環への帰結）。

## 方針
界面の存在を取り出して 環の excision の比較′ の定理へ渡す。BS 著者版 Proposition 8.5 の制限付き極限を
四つの指定普遍環の始対象性で計算し、導来対象全体の離散性を得る。
界面の D(R) の excision と 導来テンソル積の比較・ホモトピー引き戻しの長完全列 の指定四辺の長完全列から、H⁰ の短完全列と
環の引き戻しを導く。単位の自然性と環の普遍性で元の四辺に同定する。

## 規約
この公開入口は以前 BS 著者版 Corollary 8.12 の文献入力であったが、現在は直接の未証明箇所を持たない。
根拠は BS 著者版 Lemma 8.4（pp.63–64）、Proposition 8.5（pp.64–65）、
Corollary 8.11、Corollary 8.12、
Corollary 8.14（p.70）。照合は
`formalization-plans/bhatt-scholze/perfectoidization-interface.md` §3・§6 に記録する。
原典：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf 。
差写像の全射性は 界面から得る環の定理 の定理として公開し、この Inputs の公開型には追加しない。

## 使われ方
同じ四つの環・単位・`IsPerfectoidization.map` の引き戻しを CLMST の降下と Tor 比較 に供給する。
-/
theorem perfectoidization_excision_isPullback
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : S →ₐ[R] T) (I : Ideal S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hI : IsModuleComplete S (p : S) (ModuleCat.of S I))
    (harc : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
      ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
      ∀ k : S →+* V, ¬ (I ≤ RingHom.ker k) → ∃! l : T →+* V, l.comp f.toRingHom = k)
    {C D Q E : Type u} [CommRing C] [CommRing D] [CommRing Q] [CommRing E]
    {ηS : S →+* C} {ηT : T →+* D} {ηQ : S ⧸ I →+* Q} {ηE : T ⧸ I.map f.toRingHom →+* E}
    (hC : IsPerfectoidization p ηS) (hD : IsPerfectoidization p ηT)
    (hQ : IsPerfectoidization p ηQ) (hE : IsPerfectoidization p ηE) :
    IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hC hD f.toRingHom))
      (CommRingCat.ofHom (IsPerfectoidization.map hC hQ (Ideal.Quotient.mk I)))
      (CommRingCat.ofHom (IsPerfectoidization.map hD hE (Ideal.Quotient.mk (I.map f.toRingHom))))
      (CommRingCat.ofHom (IsPerfectoidization.map hQ hE
        (Ideal.quotientMap (I.map f.toRingHom) f.toRingHom Ideal.le_comap_map))) := by
  exact PerfectoidizationInterface.perfectoidization_excision_isPullback R S T p hR
    (Classical.choice (exists_perfectoidizationInterfaceE3 R p hR))
    f I hS hT hI harc hC hD hQ hE

end SerrePositivity.BhattScholze.Inputs

end ArcExcision
