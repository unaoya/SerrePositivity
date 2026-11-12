module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualRightLaxBoundary
public import SerrePositivity.KST.SConstruction.DGKFixedNullPerfectZeroIso

/-!
概要：共通実右面の二零辺を、包含・商比較と同じ四頂点成分で比較する。
方針：元 V の全対象商の零性を使い、元全辺の比較を指定端点付き証人にする。
規約：零角を選び直さず、両側面に同じ零角成分を使う。
使われ方：実右面の四境界比較を全四角形比較へ貼る。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants

open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "VInput" => dgIdentityHomGluingNullInput R (U)
local notation "Z" => dgKInputStableValue R (dgFixedNullInput R (VInput))
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d)
local notation "hZ" => dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R (VInput))

/-- 概要：元実右面の零左辺の固定 ν 完全射。
方針：同じ元全対象商包含を写す。
規約：元 V と零角を保持。使われ方：指定零左側面。 -/
def dgOdotMilnorActualRightNullLeftMap :=
  dgKInputNuMap R (dgFixedNullLeft R (A := VInput))

/-- 概要：元実右面の零上辺の固定 ν 完全射。
方針：同じ対象別収縮からの商延長を写す。
規約：元商延長を保持。使われ方：指定零上側面。 -/
def dgOdotMilnorActualRightNullTopMap :=
  dgKInputNuMap R (dgFixedNullTop R (dgIdentityHomGluingNullContracted R (U)))

/-- 概要：元実零角から絶対零角への共有完全射。
方針：元全対象商からの toZeroCategory を使用する。
規約：両零側面で同じ辺。使われ方：共有零角の指定経路。 -/
def dgOdotMilnorActualRightNullZeroMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (Z) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z)

/-- 概要：共有零角成分の Cat^perf 辺は可逆。
方針：同じ全対象商の指定零頂点同型の逆を回収する。
規約：元辺を保持。使われ方：零側面比較の端点可逆性。 -/
lemma dgOdotMilnorActualRightNullZeroMap_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (perfectStableArrow (dgOdotMilnorActualRightNullZeroMap R d)
      (hZ) perfectZeroCategory_isIdempotentComplete).toTruncated := by
  change IsIso (dgKFixedNullPerfectZeroIso R (VInput)).inv
  infer_instance

/-- 概要：元実零左辺の全比較は包含側と同じ始域成分・共有零角成分を持つ。
方針：標準零圏への全自然同型を同じ指定二成分で読む。
規約：両端点の全経路を保持。使われ方：四境界比較の零左側面。 -/
def dgOdotMilnorActualRightZeroLeftWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorActualRightNullLeftMap R d) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Q))
    (dgOdotMilnorActualRightSourceMap R d) (dgOdotMilnorActualRightNullZeroMap R d)
    (dgKInputStableValue_isIdempotentComplete R (VInput)) (hZ) (hQ)
    perfectZeroCategory_isIdempotentComplete :=
  perfectStableArrowSquareWitness _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _)
      (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _))

/-- 概要：元実零上辺の全比較は共有零角成分・商側と同じ終域成分を持つ。
方針：元零角の零性を同じ元完全射で運び、全零図式を比較する。
規約：元全辺と両端点の経路を保持。使われ方：四境界比較の零上側面。 -/
def dgOdotMilnorActualRightZeroTopWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorActualRightNullTopMap R d) (fromZeroCategory (Q))
    (dgOdotMilnorActualRightNullZeroMap R d) (dgOdotMilnorActualRightTargetMap R d)
    (hZ) (dgKInputStableValue_isIdempotentComplete R
      (dgOdotMilnorRightAxisIdentityDifferenceInput R d))
    perfectZeroCategory_isIdempotentComplete (hQ) := by
  let f := dgOdotMilnorActualRightNullTopMap R d
  let b := dgOdotMilnorActualRightTargetMap R d
  let g := fromZeroCategory (Q)
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.hom := f.isExact
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor b.hom := b.isExact
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor g.hom := g.isExact
  apply perfectStableArrowSquareWitness
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _
    (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := b.hom) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := f.hom) z
        (dgFixedNullInput_isZeroCategory R (VInput) z)))
    (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := g.hom)
      ((dgOdotMilnorActualRightNullZeroMap R d).hom.app (Opposite.op ⦋0⦌) z)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _))

end SerrePositivity.KST.SConstruction
