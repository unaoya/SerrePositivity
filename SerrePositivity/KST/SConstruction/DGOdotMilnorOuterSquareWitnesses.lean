module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterAbsoluteSquare
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterNuSquare
public import SerrePositivity.KST.SConstruction.DGKFixedNullPerfectZeroIso
public import SerrePositivity.KST.SConstruction.PerfectStableArrowSquareComparison

/-!
概要：元実始域外周の指定四側面を、共通四頂点経路を持つ全ホモトピーで構成する。
方針：元包含・商比較と元零二側面の全自然性を同じ四辺証人へ移す。
規約：元始域の増大屋根・resolved 商・実完備化射を保持する。
使われ方：元 LT 外周への指定三境界付き全比較の接合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "Src" => dgKInputStableValue R (dgOdotMilnorSourceCellInput R d)
local notation "Mid" => dgKInputStableValue R (dgOdotMilnorCellInput R d)
local notation "Z" => dgKInputStableValue R (dgFixedNullInput R (dgOdotMilnorSourceCellInput R d))
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "A₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d
local notation "Λ" => dgOdotMilnorLaxCategory R d
local notation "hC" => dgKInputStableValue_isIdempotentComplete R _
local notation "hA" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d
local notation "hL" => perfectLaxCategory_isIdempotentComplete
  (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)
  (dgOdotMilnorLaxLeft_complete R d) (dgOdotMilnorLaxRight_complete R d)
local notation "h₀" => perfectZeroCategory_isIdempotentComplete

/-- 概要：同じ元外周零角から標準零圏への共有完全射。
方針：元の toZeroCategory を使う。規約：元零角を保持。
使われ方：元外周の両零側面の共有頂点経路。 -/
def dgOdotMilnorOuterNullZeroMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (Z) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z)

/-- 概要：同じ元商終域を保持する恒等完全射。
方針：元の完全恒等射を使う。規約：resolved 終域を置換しない。
使われ方：元外周の商辺・零上辺の共有頂点経路。 -/
def dgOdotMilnorOuterTargetComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (Q) (Q) := 𝟙 (Q)

/-- 概要：元外周の共有零角経路は既存指定零同型の逆として可逆。
方針：元の全対象商の完備零同型を回収する。
規約：新しい頂点同型を選ばない。使われ方：両零側面の全比較。 -/
lemma dgOdotMilnorOuterNullZeroMap_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (perfectStableArrow (dgOdotMilnorOuterNullZeroMap R d) (hC) (h₀)).toTruncated := by
  change IsIso (dgKFixedNullPerfectZeroIso R (dgOdotMilnorSourceCellInput R d)).inv
  infer_instance

/-- 概要：元実外周包含の全比較と同じ指定二頂点経路を保持する。
方針：元包含全自然性を元四辺ホモトピーへ移す。
規約：元始域の増大屋根を保持。使われ方：外周下面の第一側面。 -/
def dgOdotMilnorOuterInclusionWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorNuSourceInclusion R d) (dgOdotMilnorLaxInclusion R d)
    (dgOdotMilnorOuterSourceComparison R d) (dgOdotMilnorOuterMiddleComparison R d)
    (hC) (hC) (hA) (hL) :=
  perfectStableArrowSquareWitness _ _ _ _ (hC) (hC) (hA) (hL)
    (dgOdotMilnorOuterInclusionComparison R d)

/-- 概要：元実外周商辺の全比較と同じ指定二頂点経路を保持する。
方針：元射影の全比較を元四辺ホモトピーへ移す。
規約：同じ resolved 商・実 c を保持。使われ方：外周下面の第二側面。 -/
def dgOdotMilnorOuterProjectionWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorCellProjectionExactMap R d) (dgOdotMilnorOuterCompletedProjection R d h)
    (dgOdotMilnorOuterMiddleComparison R d) (dgOdotMilnorOuterTargetComparison R d)
    (hC) (hC) (hL) (hC) :=
  perfectStableArrowSquareWitness _ _ _ _ (hC) (hC) (hL) (hC)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgOdotMilnorOuterProjectionComparison R d h).symm
      (Category.comp_id _).symm rfl)

/-- 概要：元実外周零左辺の全比較と同じ始域・共有零角経路を保持する。
方針：元標準零圏値の全自然比較を元四辺ホモトピーへ移す。
規約：同じ頂点経路を保持。使われ方：外周上面の第一側面。 -/
def dgOdotMilnorOuterZeroLeftWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorOuterNullLeftMap R d) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (A₀))
    (dgOdotMilnorOuterSourceComparison R d) (dgOdotMilnorOuterNullZeroMap R d)
    (hC) (hC) (hA) (h₀) :=
  perfectStableArrowSquareWitness _ _ _ _ (hC) (hC) (hA) (h₀)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _) (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _))

/-- 概要：元実外周零上辺の全比較と同じ共有零角・終域経路を保持する。
方針：元零角の全零性と元上辺の完全性から全比較を作る。
規約：元合成延長を保持。使われ方：外周上面の第二側面。 -/
def dgOdotMilnorOuterZeroTopWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorOuterNullTopMap R d) (fromZeroCategory (Q))
    (dgOdotMilnorOuterNullZeroMap R d) (dgOdotMilnorOuterTargetComparison R d)
    (hC) (hC) (h₀) (hC) := by
  let f := dgOdotMilnorOuterNullTopMap R d
  let g := fromZeroCategory (Q)
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor g.hom := g.isExact
  apply perfectStableArrowSquareWitness _ _ _ _ (hC) (hC) (h₀) (hC)
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso f.hom ((dgOdotMilnorOuterNullZeroMap R d).hom ≫ g.hom)
      (fun z => @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ f.hom f.isExact z
        (dgFixedNullInput_isZeroCategory R (dgOdotMilnorSourceCellInput R d) z))
      (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := g.hom)
        ((dgOdotMilnorOuterNullZeroMap R d).hom.app _ z) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _)))
    (Category.comp_id _).symm rfl
end SerrePositivity.KST.SConstruction
