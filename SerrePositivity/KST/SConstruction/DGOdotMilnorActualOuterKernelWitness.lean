module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualOuterNuBoundary
public import SerrePositivity.KST.SConstruction.DGKFixedNullPerfectZeroIso

/-!
概要：実外周と元厚核零化面の四辺を同じ四頂点成分で比較する。
方針：元包含の恒等成分・元商比較の指定終域成分・両全対象商の零同型を使う。
規約：元 V 零角と元厚核零角を保持し、四側面で共有する経路を固定する。
使われ方：実外周の全四角形比較を貼る四つの指定端点付き証人。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "KIn" => dgOdotMilnorFlatKernelInput R d
local notation "PIn" => dgOdotMilnorCellInput R d
local notation "VIn" => dgIdentityHomGluingNullInput R (U)
local notation "DIn" => dgOdotMilnorRightAxisIdentityDifferenceInput R d
local notation "QIn" => dgOdotMilnorResolvedInput R d
local notation "ZV" => dgKInputStableValue R (dgFixedNullInput R (VIn))
local notation "ZK" => dgKInputStableValue R (dgFixedNullInput R (KIn))
local notation "hK" => dgKInputStableValue_isIdempotentComplete R (KIn)
local notation "hP" => dgKInputStableValue_isIdempotentComplete R (PIn)
local notation "hD" => dgKInputStableValue_isIdempotentComplete R (DIn)
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (QIn)
local notation "hZV" => dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R (VIn))
local notation "hZK" => dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R (KIn))

/-- 概要：元 V 零角から元厚核零角への共有完全射。
方針：両元全対象商の指定零比較の合成を使う。
規約：零角を別頂点に置換しない。使われ方：両零側面の共有経路。 -/
def dgOdotMilnorActualOuterKernelZeroMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (ZV) (ZK) where
  hom := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (ZV)).hom ≫ (fromZeroCategory (ZK)).hom
  isExact := @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (ZV)).isExact (fromZeroCategory (ZK)).isExact

/-- 概要：両元零角間の共有辺は Cat^perf 内で可逆。
方針：同じ元二零同型の逆と順射の合成を元完全合成則で回収する。
規約：元の完全射を保持。使われ方：零側面の指定端点可逆性。 -/
lemma dgOdotMilnorActualOuterKernelZeroMap_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (perfectStableArrow (dgOdotMilnorActualOuterKernelZeroMap R d)
      (hZV) (hZK)).toTruncated := by
  change IsIso (perfectStableHoArrow (dgOdotMilnorActualOuterKernelZeroMap R d) (hZV) (hZK))
  have h : perfectStableHoArrow (dgOdotMilnorActualOuterKernelZeroMap R d) (hZV) (hZK) =
      ((dgKFixedNullPerfectZeroIso R (VIn)).symm ≪≫
        dgKFixedNullPerfectZeroIso R (KIn)).hom :=
    perfectStableHoArrow_comp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (ZV)) (fromZeroCategory (ZK))
      (hZV) perfectZeroCategory_isIdempotentComplete (hZK)
  exact (congrArg (fun fm => IsIso fm) h).mpr
    (((dgKFixedNullPerfectZeroIso R (VIn)).symm ≪≫
      dgKFixedNullPerfectZeroIso R (KIn)).isIso_hom)

/-- 概要：実外周の元包含辺と厚核零化面の元包含辺は恒等二成分で比較される。
方針：同じ元完全射の恒等合成式を指定二端点付き証人へ渡す。
規約：両元辺を保持。使われ方：外周比較の包含側面。 -/
def dgOdotMilnorActualOuterKernelInclusionWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorFlatKernelExactMap R d) (dgOdotMilnorFlatKernelExactMap R d)
    (𝟙 (dgKInputStableValue R (KIn))) (𝟙 (dgKInputStableValue R (PIn)))
    (hK) (hP) (hK) (hP) := by
  let f := (dgOdotMilnorFlatKernelExactMap R d).hom
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f := Iso.refl (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
  apply perfectStableArrowSquareWitness
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e (Category.comp_id f).symm (Category.id_comp f).symm

/-- 概要：実外周の商辺は恒等始域成分と元指定終域評価で元 cell 商辺へ比較される。
方針：保存済みの元厳密合成辺の全比較を同じ二成分付き証人へ渡す。
規約：元 cell 始域と同じ終域同値。使われ方：外周比較の商側面。 -/
def dgOdotMilnorActualOuterKernelProjectionWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorActualOuterProjectionMap R d) (dgOdotMilnorCellProjectionExactMap R d)
    (𝟙 (dgKInputStableValue R (PIn))) (dgOdotMilnorActualRightTargetMap R d)
    (hP) (hD) (hP) (hQ) := by
  apply perfectStableArrowSquareWitness
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgOdotMilnorActualOuterProjectionComparison R d) rfl
    (Category.id_comp (dgOdotMilnorCellProjectionExactMap R d).hom).symm

/-- 概要：二つの元零左辺は同じ恒等始域成分と共有零角成分で比較される。
方針：元厚核全対象商の零性から全自然比較を作る。
規約：元四頂点経路を保持。使われ方：外周比較の零左側面。 -/
def dgOdotMilnorActualOuterKernelZeroLeftWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorActualOuterNullLeftMap R d)
    (dgKInputNuMap R (dgFixedNullLeft R (A := KIn)))
    (𝟙 (dgKInputStableValue R (KIn))) (dgOdotMilnorActualOuterKernelZeroMap R d)
    (hK) (hZV) (hK) (hZK) :=
  perfectStableArrowSquareWitness _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso (X := (ZK).obj) _ _
      (fun _ => dgFixedNullInput_isZeroCategory R (KIn) _)
      (fun _ => dgFixedNullInput_isZeroCategory R (KIn) _))

/-- 概要：二つの元零上辺は共有零角成分と同じ元終域評価で比較される。
方針：元 V 零角の零性を元完全射で運び、元厚核零角側の像と全比較する。
規約：元四頂点経路を保持。使われ方：外周比較の零上側面。 -/
def dgOdotMilnorActualOuterKernelZeroTopWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorActualRightNullTopMap R d)
    (dgKInputNuMap R (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d)))
    (dgOdotMilnorActualOuterKernelZeroMap R d) (dgOdotMilnorActualRightTargetMap R d)
    (hZV) (hD) (hZK) (hQ) := by
  let f := dgOdotMilnorActualRightNullTopMap R d
  let b := dgOdotMilnorActualRightTargetMap R d
  let g := dgKInputNuMap R (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.hom := f.isExact
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor b.hom := b.isExact
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor g.hom := g.isExact
  apply perfectStableArrowSquareWitness
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso (X := (dgKInputStableValue R (QIn)).obj) _ _
    (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := b.hom) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := f.hom) z (dgFixedNullInput_isZeroCategory R (VIn) z)))
    (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := g.hom) _
      (dgFixedNullInput_isZeroCategory R (KIn) _))

end SerrePositivity.KST.SConstruction
