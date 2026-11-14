module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityZeroSideWitnesses
public import SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyInvertibility

/-!
概要：恒等実右面の四辺比較を、同じ四頂点経路を保つ一つの境界比較へ束ねる。
方針：指定全辺証人の端点経路を照合し、絶対提示の四辺を回収する。
規約：D2 比較は明示入力。境界比較を全四角形の存在証明と数えない。
使われ方：元両二単体を固定した上下 prism の共通側境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d)

/-- 概要：絶対恒等列の零左辺は元の Cat^perf 零完全射の全一単体。
方針：元 raw 四辺式を充満忠実な包含で検出する。
規約：元提示を保持。使われ方：実左辺比較の終端照合。 -/
lemma dgOdotMilnorIdentityAbsoluteSquare_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square =
      SSet.yonedaEquiv.symm (perfectStableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Q))
        (hQ) perfectZeroCategory_isIdempotentComplete).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ perfectVerdierSquare _ ) ≫ _ = _
  rw [Category.assoc, perfectVerdierSquare_inclusion]
  exact (perfectIdentityLaxRawSquare_edges (Q) (hQ)).2.2.1.trans
    (perfectStableArrow_inclusion _ _ _).symm

/-- 概要：絶対恒等列の零上辺は元の Cat^perf 零完全射の全一単体。
方針：元 raw 四辺式を充満忠実な包含で検出する。
規約：元提示を保持。使われ方：実上辺比較の終端照合。 -/
lemma dgOdotMilnorIdentityAbsoluteSquare_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square =
      SSet.yonedaEquiv.symm (perfectStableArrow (fromZeroCategory (Q))
        perfectZeroCategory_isIdempotentComplete (hQ)).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ perfectVerdierSquare _ ) ≫ _ = _
  rw [Category.assoc, perfectVerdierSquare_inclusion]
  exact (perfectIdentityLaxRawSquare_edges (Q) (hQ)).2.1.trans
    (perfectStableArrow_inclusion _ _ _).symm

/-- 概要：元ホモトピーの全写像を保ち端点だけを指定等号で表示する。
方針：元写像と元端点式を使う。規約：経路を選び直さない。
使われ方：四境界を共有頂点経路で束ねる。 -/
def specifiedSquareHomotopyWithEndpoints {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') : SSet.Homotopy f' g' where
  h := H.h
  h₀ := H.h₀.trans hf
  h₁ := H.h₁.trans hg
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

namespace DGOdotMilnorIdentityLaxComparisonInput
variable (v : DGOdotMilnorIdentityLaxComparisonInput R d)

/-- 概要：元下辺を指定元ホモトピーで比較する。
方針：同じ対角証人の端点表示を回収する。規約：全写像を保持。
使われ方：下面の第一側面。 -/
def bottomHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) :=
  specifiedSquareHomotopyWithEndpoints v.diagonalWitness.homotopy
    (dgOdotMilnorIdentityNullSquare_perfect_diagonal R d).symm
    (PerfectVerdierSequence.presentation_bottom (perfectIdentityLaxSequence (Q) (hQ))).symm

/-- 概要：元右辺を指定元ホモトピーで比較する。
方針：同じ差証人の端点表示を回収する。規約：全写像を保持。
使われ方：下面の第二側面。 -/
def rightHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) :=
  specifiedSquareHomotopyWithEndpoints v.differenceWitness.homotopy
    (dgOdotMilnorIdentityNullSquare_perfect_difference R d).symm (by
      rw [PerfectVerdierSequence.presentation_right, perfectIdentityLaxSequence_projection]
      rfl)

/-- 概要：元零左辺を指定元ホモトピーで比較する。
方針：同じ零左辺証人の端点表示を回収する。規約：全写像を保持。
使われ方：上面の第一側面。 -/
def leftHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) :=
  specifiedSquareHomotopyWithEndpoints (zeroLeftWitness R d).homotopy
    (dgOdotMilnorIdentityNullSquare_perfect_left R d).symm
    (dgOdotMilnorIdentityAbsoluteSquare_left R d).symm

/-- 概要：元零上辺を指定元ホモトピーで比較する。
方針：同じ零上辺証人の端点表示を回収する。規約：全写像を保持。
使われ方：上面の第二側面。 -/
def topHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) :=
  specifiedSquareHomotopyWithEndpoints v.zeroTopWitness.homotopy
    (dgOdotMilnorIdentityNullSquare_perfect_top R d).symm
    (dgOdotMilnorIdentityAbsoluteSquare_top R d).symm

/-- 概要：同じ元 bottom 側面比較の辺は可逆。
方針：同じ指定二頂点の可逆性を使う。規約：元全ホモトピーを保持。
使われ方：四境界比較の点ごとの可逆性。 -/
lemma bottomHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy v.bottomHomotopy) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy v.bottomHomotopy)
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy v.diagonalWitness.homotopy) rfl).mpr
      (v.diagonalWitness.isInvertible
        (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
          (dgOdotMilnorIdentityBaseValueEquivalence R d).isQCatEquivalence)
        (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
          v.completedGluing.isQCatEquivalence))

/-- 概要：同じ元 right 側面比較の辺は可逆。
方針：同じ指定二頂点の可逆性を使う。規約：元全ホモトピーを保持。
使われ方：四境界比較の点ごとの可逆性。 -/
lemma rightHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy v.rightHomotopy) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy v.rightHomotopy)
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy v.differenceWitness.homotopy) rfl).mpr
      (v.differenceWitness.isInvertible
        (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
          v.completedGluing.isQCatEquivalence)
        (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
          (v.difference.trans (dgOdotMilnorIdentityBaseValueEquivalence R d)).isQCatEquivalence))

/-- 概要：同じ元 left 側面比較の辺は可逆。
方針：同じ指定二頂点の可逆性を使う。規約：元全ホモトピーを保持。
使われ方：四境界比較の点ごとの可逆性。 -/
lemma leftHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (leftHomotopy R d)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (leftHomotopy R d))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (zeroLeftWitness R d).homotopy) rfl).mpr
      ((zeroLeftWitness R d).isInvertible
        (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
          (dgOdotMilnorIdentityBaseValueEquivalence R d).isQCatEquivalence)
        (dgOdotMilnorIdentityNullZeroMap_isInvertible R d))

/-- 概要：同じ元 top 側面比較の辺は可逆。
方針：同じ指定二頂点の可逆性を使う。規約：元全ホモトピーを保持。
使われ方：四境界比較の点ごとの可逆性。 -/
lemma topHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy v.topHomotopy) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy v.topHomotopy)
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy v.zeroTopWitness.homotopy) rfl).mpr
      (v.zeroTopWitness.isInvertible (dgOdotMilnorIdentityNullZeroMap_isInvertible R d)
        (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
          (v.difference.trans (dgOdotMilnorIdentityBaseValueEquivalence R d)).isQCatEquivalence))

/-- 概要：元 lowerLeft の二側面は同じ頂点経路を持つ。
方針：元証人の指定端点式を使う。規約：経路を変更しない。
使われ方：元四境界の接合。 -/
lemma lowerLeftHomotopy_path :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (v.bottomHomotopy).h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (leftHomotopy R d).h :=
  v.diagonalWitness.source_path.trans (zeroLeftWitness R d).source_path.symm

/-- 概要：元 lowerRight の二側面は同じ頂点経路を持つ。
方針：元証人の指定端点式を使う。規約：経路を変更しない。
使われ方：元四境界の接合。 -/
lemma lowerRightHomotopy_path :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (v.bottomHomotopy).h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (v.rightHomotopy).h :=
  v.diagonalWitness.target_path.trans v.differenceWitness.source_path.symm

/-- 概要：元 upperLeft の二側面は同じ頂点経路を持つ。
方針：元証人の指定端点式を使う。規約：経路を変更しない。
使われ方：元四境界の接合。 -/
lemma upperLeftHomotopy_path :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (v.topHomotopy).h =
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (leftHomotopy R d).h :=
  v.zeroTopWitness.source_path.trans (zeroLeftWitness R d).target_path.symm

/-- 概要：元 upperRight の二側面は同じ頂点経路を持つ。
方針：元証人の指定端点式を使う。規約：経路を変更しない。
使われ方：元四境界の接合。 -/
lemma upperRightHomotopy_path :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (v.topHomotopy).h =
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ (v.rightHomotopy).h :=
  v.zeroTopWitness.target_path.trans v.differenceWitness.target_path.symm

/-- 概要：元実右面と絶対恒等面の全四境界比較は同じ四頂点経路を共有する。
方針：同じ四辺証人の端点式と二端点可逆性を使う。
規約：元両面・全四辺を保持。使われ方：上下二胞体の比較 prism の構成。 -/
def squareFrameComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) where
  bottom := v.bottomHomotopy
  right := v.rightHomotopy
  left := leftHomotopy R d
  top := v.topHomotopy
  lower_left := v.lowerLeftHomotopy_path
  lower_right := v.lowerRightHomotopy_path
  upper_left := v.upperLeftHomotopy_path
  upper_right := v.upperRightHomotopy_path
  bottom_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge _ v.bottomHomotopy_isInvertible
  right_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge _ v.rightHomotopy_isInvertible
  left_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge _ (leftHomotopy_isInvertible R d)
  top_invertible := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge _ v.topHomotopy_isInvertible
end DGOdotMilnorIdentityLaxComparisonInput
end SerrePositivity.KST.SConstruction
