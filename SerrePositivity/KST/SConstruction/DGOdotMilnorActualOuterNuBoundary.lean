module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualOuterEdges
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisCompositeNu
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualRightZeroWitness
public import SerrePositivity.KST.SConstruction.DGOdotMilnorPerfectNullSquare

/-!
概要：共通実外周と元厚核零化面の四辺を同じ固定 ν で回収する。
方針：元厳密合成の ν 合成則と、元 cell 商射影への全比較を使用する。
規約：実外周の元 V 零角と元厚核零角を区別して保持する。
使われ方：同じ四頂点成分を使う外周全図式比較の指定境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "KIn" => dgOdotMilnorFlatKernelInput R d
local notation "PIn" => dgOdotMilnorCellInput R d
local notation "VIn" => dgIdentityHomGluingNullInput R (U)
local notation "DIn" => dgOdotMilnorRightAxisIdentityDifferenceInput R d
local notation "O" => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ dgOdotMilnorActualRectangleDiagram R d

/-- 概要：実外周の元厳密合成辺の同じ固定 ν 完全射。
方針：元 S 合成辺を直接評価する。
規約：辺代表を変更しない。使われ方：元 cell 商辺との区間比較。 -/
def dgOdotMilnorActualOuterProjectionMap :=
  dgKInputNuMap R (dgOdotMilnorRightAxisInputMap R d ≫
    dgOdotMilnorRightAxisIdentityDifferenceInputMap R d)

/-- 概要：実外周の元 V 全対象商への合成辺の同じ固定 ν 完全射。
方針：元 V 因子化と元全対象商包含の合成を評価する。
規約：元零角を保持。使われ方：実外周の零左側面。 -/
def dgOdotMilnorActualOuterNullLeftMap :=
  dgKInputNuMap R (dgOdotMilnorKernelNullFactorInputMap R d ≫
    dgFixedNullLeft R (A := VIn))

/-- 概要：実外周の元合成商辺は同じ指定終域同値の下で元 cell 商辺と全比較される。
方針：固定 ν の厳密合成則を保存済み全合成比較へ渡す。
規約：元厳密合成辺を保持。使われ方：外周の商側の指定比較。 -/
def dgOdotMilnorActualOuterProjectionComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorActualOuterProjectionMap R d).hom ≫
      (dgOdotMilnorRightAxisDifferenceResolvedValueEquivalence R d).hom)
    (dgOdotMilnorCellProjectionExactMap R d).hom := by
  have nu_comp {A₀ A₁ A₂ : PerfDGInput.{u, u + 1} R} (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂) :
      (dgKInputNuMap R (f ≫ g)).hom = (dgKInputNuMap R f).hom ≫ (dgKInputNuMap R g).hom := by
    rw [dgKInputNuMap_eq, dgKInputNuMap_eq, dgKInputNuMap_eq]
    exact congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom ((presentedPerfectDGStableCategoryFunctor R).map_comp f g)
  have h := nu_comp (dgOdotMilnorRightAxisInputMap R d)
    (dgOdotMilnorRightAxisIdentityDifferenceInputMap R d)
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgOdotMilnorRightAxisCompositeNuComparison R d)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun fm => fm ≫
        (dgOdotMilnorRightAxisDifferenceResolvedValueEquivalence R d).hom) h).symm) rfl

/-- 概要：共通実外周の四辺は同じ元完全射の全区間図式。
方針：元四辺の厳密回収を固定 ν の全一単体回収へ渡す。
規約：元包含・元合成・元二零辺を保持。使われ方：四辺の指定端点付き比較。 -/
lemma dgOdotMilnorActualOuter_nu_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (O) ≫ dgKInputPerfectNu R = SSet.yonedaEquiv.symm
        (perfectStableArrow (dgOdotMilnorFlatKernelExactMap R d)
          (dgKInputStableValue_isIdempotentComplete R (KIn))
          (dgKInputStableValue_isIdempotentComplete R (PIn))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (O) ≫ dgKInputPerfectNu R = SSet.yonedaEquiv.symm
        (perfectStableArrow (dgOdotMilnorActualOuterProjectionMap R d)
          (dgKInputStableValue_isIdempotentComplete R (PIn))
          (dgKInputStableValue_isIdempotentComplete R (DIn))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (O) ≫ dgKInputPerfectNu R = SSet.yonedaEquiv.symm
        (perfectStableArrow (dgOdotMilnorActualOuterNullLeftMap R d)
          (dgKInputStableValue_isIdempotentComplete R (KIn))
          (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R (VIn)))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (O) ≫ dgKInputPerfectNu R = SSet.yonedaEquiv.symm
        (perfectStableArrow (dgOdotMilnorActualRightNullTopMap R d)
          (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R (VIn)))
          (dgKInputStableValue_isIdempotentComplete R (DIn))).edge := by
  have map_edge {A₀ A₁ : PerfDGInput.{u, u + 1} R} (f : A₀ ⟶ A₁)
      (s : (Δ[1] : SSet.{u + 2}) ⟶ (Δ[1] ⊗ Δ[1]))
      (h : s ≫ (O) = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) :
      s ≫ (O) ≫ dgKInputPerfectNu R = SSet.yonedaEquiv.symm
        (perfectStableArrow (dgKInputNuMap R f)
          (dgKInputStableValue_isIdempotentComplete R A₀)
          (dgKInputStableValue_isIdempotentComplete R A₁)).edge :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun fm => fm ≫ dgKInputPerfectNu R) h).trans
        (dgKInputPerfectNu_edge_diagram R f))
  have h := dgOdotMilnorActualOuter_edges R d
  exact ⟨map_edge _ _ h.1, map_edge _ _ h.2.1,
    map_edge _ _ h.2.2.1, map_edge _ _ h.2.2.2⟩

/-- 概要：元厚核零化面の四辺も同じ元完全射の全区間図式として回収する。
方針：保存済み元 S 四辺と固定 ν の元全一単体回収を合成する。
規約：元 thick 核と元全対象商を保持。使われ方：実外周比較の終端四境界。 -/
lemma dgOdotMilnorKernelNull_nu_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgOdotMilnorFlatKernelExactMap R d)
        (dgKInputStableValue_isIdempotentComplete R (KIn))
        (dgKInputStableValue_isIdempotentComplete R (PIn))).edge ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgOdotMilnorCellProjectionExactMap R d)
        (dgKInputStableValue_isIdempotentComplete R (PIn))
        (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d))).edge ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgKInputNuMap R (dgFixedNullLeft R (A := KIn)))
        (dgKInputStableValue_isIdempotentComplete R (KIn))
        (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R (KIn)))).edge ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgKInputNuMap R (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d)))
        (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R (KIn)))
        (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d))).edge := by
  have map_edge {A₀ A₁ : PerfDGInput.{u, u + 1} R} (f : A₀ ⟶ A₁)
      (s : (Δ[1] : SSet.{u + 2}) ⟶ (Δ[1] ⊗ Δ[1]))
      (h : s ≫ dgOdotMilnorPerfectNullSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) :
      s ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputPerfectNu R = SSet.yonedaEquiv.symm
        (perfectStableArrow (dgKInputNuMap R f)
          (dgKInputStableValue_isIdempotentComplete R A₀)
          (dgKInputStableValue_isIdempotentComplete R A₁)).edge :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun fm => fm ≫ dgKInputPerfectNu R) h).trans
        (dgKInputPerfectNu_edge_diagram R f))
  have h := dgOdotMilnorPerfectNullSquare_edges R d
  exact ⟨map_edge _ _ h.1, map_edge _ _ h.2.1,
    map_edge _ _ h.2.2.1, map_edge _ _ h.2.2.2⟩

end SerrePositivity.KST.SConstruction
