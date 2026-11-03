module

public import SerrePositivity.KST.NonConnective.DGKappaConeInput
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.KST.SConstruction.PerfDGInput

/-!
概要：明示入力の同じ κ-compact dg 小模型から、平坦 Drinfeld 懸垂を作る。
方針：実加群内の同じ full dg cone と perfect 対象を保持し、β3 の実商を適用する。
規約：入力の存在・F2N-5・反復懸垂の射作用を完成扱いしない。
使われ方：K-7 工程 b、固定された厳密 dg K 入力への懸垂の受け渡し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ実加群の全 Hom を持つ、入力として受け取った κ-compact dg cone。 -/
abbrev DGKappaCone := DGFullSubcategory (ModuleCategory R D) I.objects

instance dgKappaConeSmall : Small.{u} (DGKappaCone R D I) := I.small
instance dgKappaConePretriangulated : IsDGPretriangulated R (DGKappaCone R D I) :=
  I.pretriangulated

/-- 元の dg cone 内の実可算直和関手。全次数の Hom 作用は既に構成したものを制限する。 -/
def dgKappaConeCountableSum : DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I) :=
  (dgCountableSumFunctor R D).restrict I.objects I.objects
    (fun M hM ↦ I.countableClosed (fun _ : ℕ ↦ M) (fun _ ↦ hM))

/-- 同じ dg cone の中で、元の主導来像が perfect である対象の集合。 -/
def dgKappaConePerfectObjects : Set (DGKappaCone R D I) :=
  fun M ↦ modulePerfect R D ((moduleToDerived R D).obj M.val)

/-- 元の Hom の平坦性を仮定せず、同じ dg cone を cell 分解して取る実 Drinfeld 商。 -/
abbrev DGKappaSuspension :=
  DGQuotient.QuotientObject (DGCategoryCellResolution.Source R (DGKappaCone R D I))
    (resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))

/-- 構成した同じ平坦 Drinfeld 商の実 dg nerve。 -/
abbrev dgKappaSuspensionInfinity :=
  resolvedDGQuotientNerve R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)

/-- 元の dg cone から同じ実懸垂への商関手。 -/
def dgKappaSuspensionProjection :
    dgNerve R (DGKappaCone R D I) ⟶ dgKappaSuspensionInfinity R D I :=
  resolvedDGQuotientFunctor R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)

/-- 同じ実懸垂の nerve は安定。入力の前三角性と β3 を使う。 -/
theorem dgKappaSuspensionInfinity_isStable : IsStable (dgKappaSuspensionInfinity R D I) :=
  resolvedDGQuotientNerve_isStable R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)

/-- perfect 対象の実安定閉包から cone と懸垂への列は、同じ実 Verdier 列。 -/
theorem dgKappaSuspension_isStableVerdierSequence :
    let := dgNerve_isStable_of_pretriangulated R (DGKappaCone R D I)
    let := dgStableClosureNerve_isStable R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)
    let := dgKappaSuspensionInfinity_isStable R D I
    IsStableVerdierSequence
      (dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))
      (dgKappaSuspensionProjection R D I) :=
  resolvedDGQuotient_isStableVerdierSequence R (DGKappaCone R D I)
    (dgKappaConePerfectObjects R D I)

/-- 構成した同じ小さい dg 懸垂を、固定された厳密 dg K の入力に束ねる。 -/
def dgKappaSuspensionKInput : SConstruction.PerfDGInput R :=
  SConstruction.perfDGInputOf R (DGKappaSuspension R D I)

end SerrePositivity.KST.NonConnective
