module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLandTamme
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories
public import Mathlib.CategoryTheory.Enriched.Basic
public import SerrePositivity.KST.LocalizingInvariants.PathComparisonSquare
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle

/-!
概要：元の resolved 射影と実 lax 射影を指定二胞体で比較し、完備化まで貼る。
方針：同じ lax 同値の単位から作った比較三角形を全四角形に実現する。
規約：上下の合成三角形を保持し、完備化射の局所化性は仮定しない。
使われ方：完備化付き相対 Verdier 長方形の商境界の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d

local notation "E" => dgOdotMilnorNativeLaxComparison R d
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d
local notation "r" => dgOdotMilnorLaxProjection R d

/-- 概要：元の射影比較の指定二胞体を持つ実比較三角形。
方針：同じ単位二胞体を写像空間の辺へ移す。規約：射の類の等号で代用しない。
使われ方：商境界の全図式比較。 -/
def dgOdotMilnorProjectionComparisonTriangle :
    SSet.Edge.CompStruct (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeMiddle R d)))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeMiddle R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d) from ⟨(E).hom ≫ (r).hom,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp (E).hom (r).hom⟩)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (q)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactMapComparisonTriangle (F := q)
    (G := ⟨(E).hom ≫ (r).hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp (E).hom (r).hom⟩)
    (dgOdotMilnorLaxProjection_comparison R d).symm

/-- 概要：同じ実 lax 射影の合成三角形を元の resolved 射影に沿って移す。
方針：指定三次元充填を保持する Sp の構成を使う。規約：元の射影を対角に固定する。
使われ方：長方形の下合成三角形。 -/
def dgOdotMilnorProjectionComposition :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (E)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (r)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (q)) :=
  (compositionDiagonalTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (E) (r))
    (dgOdotMilnorProjectionComparisonTriangle R d)).triangle

/-- 概要：元 gluing・lax 模型・resolved 商の全比較四角形。
方針：元の比較三角形と恒等左辺の三角形を貼る。規約：四辺を厳密に保持する。
使われ方：完備化前の商境界の実比較。 -/
def dgOdotMilnorProjectionComparisonSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} :=
  PathComparisonSquare.square
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (E) (r))
    (SSet.Edge.CompStruct.idComp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (q)))
    (dgOdotMilnorProjectionComparisonTriangle R d)

/-- 概要：比較四角形の四辺は同じ lax 比較・resolved 射影・恒等・lax 射影。
方針：貼り合わせの四つの境界則を使用する。規約：全一単体で固定する。
使われ方：包含との貼合せで使う指定商境界。 -/
lemma dgOdotMilnorProjectionComparisonSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorProjectionComparisonSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (E)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorProjectionComparisonSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (q)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorProjectionComparisonSquare R d =
        SSet.yonedaEquiv.symm (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeMiddle R d))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorProjectionComparisonSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (r)).edge :=
  ⟨PathComparisonSquare.square_bottom _ _ _, PathComparisonSquare.square_top _ _ _,
    PathComparisonSquare.square_left _ _ _, PathComparisonSquare.square_right _ _ _⟩

/-- 概要：実比較面の下三角形は同じ指定二胞体による移送そのもの。
方針：貼り合わせの制限を回収する。規約：別の三角形を選択しない。
使われ方：完備化長方形の下境界。 -/
lemma dgOdotMilnorProjectionComparisonSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotMilnorProjectionComparisonSquare R d =
      SSet.yonedaEquiv.symm (dgOdotMilnorProjectionComposition R d).simplex :=
  PathComparisonSquare.square_lower _ _ _

variable (c : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d)
  (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)))

/-- 概要：元 resolved 射影と指定 c の実合成三角形。
方針：元の完全射の合成をそのまま coherent nerve に写す。
規約：中間の native 商を保持する。使われ方：長方形の上境界。 -/
def dgOdotMilnorCompletionComposition : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (q))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow c) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeMiddle R d)
      (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)) from
        ⟨(q).hom ≫ c.hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp (q).hom c.hom⟩)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (q) c

/-- 概要：完備化後も元の resolved 射影比較を同じ全関手同型で保持する。
方針：指定単位二胞体を同じ c で後合成する。規約：hc を不要な比較へ仮定しない。
使われ方：Cat^perf の右射境界。 -/
def dgOdotMilnorCompletedProjectionComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((E).hom ≫ ((r).hom ≫ c.hom)) ((q).hom ≫ c.hom) := by
  rw [← Category.assoc]
  exact (dgOdotMilnorLaxProjection_comparison R d).postcomp c.hom

/-- 概要：同じ完備化射を二辺に持つ実合成四角形。
方針：同じ合成三角形を二度使う。規約：resolved 商を途中頂点として保持する。
使われ方：射影比較面と貼る右面。 -/
def dgOdotMilnorCompletionCompositionSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} :=
  PathComparisonSquare.square
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (r) c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (r) c)
    (SSet.Edge.CompStruct.idComp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgOdotMilnorLaxCategory R d)
        (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)) from
          ⟨(r).hom ≫ c.hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp (r).hom c.hom⟩)))

/-- 概要：合成面の二つの横辺は lax 射影と c、左辺も同じ lax 射影。
方針：四辺固定の構成を回収する。規約：完備化射を選び直さない。
使われ方：指定合成三角形を持つ長方形の貼合せ。 -/
lemma dgOdotMilnorCompletionCompositionSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorCompletionCompositionSquare R d c =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (r)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorCompletionCompositionSquare R d c =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow c).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorCompletionCompositionSquare R d c =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (r)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorCompletionCompositionSquare R d c =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow c).edge :=
  ⟨PathComparisonSquare.square_bottom _ _ _, PathComparisonSquare.square_top _ _ _,
    PathComparisonSquare.square_left _ _ _, PathComparisonSquare.square_right _ _ _⟩

/-- 概要：元 resolved 射影・lax 比較・指定完備化を全体として保つ実長方形。
方針：同じ二面と上下の指定合成三角形を Sp の prism 充填で貼る。
規約：Verdier 零角を持つ S 内長方形の存在とは区別する。
使われ方：d④ の全比較に必要な商射影側の具体的境界。 -/
def dgOdotMilnorProjectionRectangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquarePastingRectangle
    (dgOdotMilnorProjectionComparisonSquare R d)
    (dgOdotMilnorCompletionCompositionSquare R d c)
    (SSet.yonedaEquiv.symm (dgOdotMilnorProjectionComposition R d).simplex)
    (SSet.yonedaEquiv.symm (dgOdotMilnorCompletionComposition R d c).simplex) := by
  have hL := dgOdotMilnorProjectionComparisonSquare_edges R d
  have hR := dgOdotMilnorCompletionCompositionSquare_edges R d c
  apply Classical.choice
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.nonempty_squarePastingRectangle
  · exact hL.2.2.2.trans hR.2.2.1.symm
  · rw [hL.1, stdSimplex.δ_comp_yonedaEquiv_symm,
      (dgOdotMilnorProjectionComposition R d).d₂]
  · rw [hR.1, stdSimplex.δ_comp_yonedaEquiv_symm,
      (dgOdotMilnorProjectionComposition R d).d₀]
  · rw [hL.2.1, stdSimplex.δ_comp_yonedaEquiv_symm,
      (dgOdotMilnorCompletionComposition R d c).d₂]
  · rw [hR.2.1, stdSimplex.δ_comp_yonedaEquiv_symm,
      (dgOdotMilnorCompletionComposition R d c).d₀]

end SerrePositivity.KST.SConstruction
