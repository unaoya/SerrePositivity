module
public import SerrePositivity.KST.NonConnective.DGKappaConePerfectRepleteness
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionDescent
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKMap

/-!
概要：perfect を反映する cone 同値の逆を、同じ元の実懸垂商へ下降する。
方針：逆像を元の実 cone 頂点で表し、perfect の頂点同型不変性と反映で零化する。
規約：元の quotient と指定 cone 同値の逆を保持し、厳密な逆 dg 関手は要求しない。
使われ方：K-7 e の実懸垂射の Morita 同値性。無条件の入力作用は別工程。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R C κ) (J : DGKappaConeInput R D κ)
  (M : DGKappaSuspensionMapData R C D I J)
  (hf : IsQCatEquivalence (dgNerve.map M.cone))
local instance inverseDescentConeStable : IsStable (dgNerve R (DGKappaCone R D J)) :=
  dgNerve_isStable_of_pretriangulated R _
local instance inverseDescentSourceStable : IsStable (dgNerve R (DGKappaCone R C I)) :=
  dgNerve_isStable_of_pretriangulated R _
local instance inverseDescentQuotientStable : IsStable (dgKappaSuspensionInfinity R C I) :=
  dgKappaSuspensionInfinity_isStable R C I

local instance inverseDescentKernelStable : IsStable
    (dgStableClosureNerve R (DGKappaCone R C I) (dgKappaConePerfectObjects R C I)) :=
  dgStableClosureNerve_isStable R _ _

/-- 同じ指定 cone 同値の逆の後に、元の源の実商射を合成する。 -/
def dgKappaSuspensionInverseSource :
    dgNerve R (DGKappaCone R D J) ⟶ dgKappaSuspensionInfinity R C I :=
  hf.choose.inv ≫ dgKappaSuspensionProjection R C I

theorem dgKappaSuspensionInverseSource_isExact :
    IsExactFunctor (dgKappaSuspensionInverseSource R C D I J M hf) := by
  let : IsExactFunctor hf.choose.inv :=
    isExactFunctor_of_isQCatEquivalence hf.choose.symm.isQCatEquivalence
  let : IsExactFunctor (dgKappaSuspensionProjection R C I) :=
    (dgKappaSuspension_isStableVerdierSequence R C I).quotientExact
  exact isExactFunctor_comp _ _

variable (hr : ∀ x : DGKappaCone R C I,
  M.cone.obj x ∈ dgKappaConePerfectObjects R D J → x ∈ dgKappaConePerfectObjects R C I)

include hr in
/-- 逆像の実頂点を回収し、同じ元の perfect 集合の全対象を零化する。 -/
theorem dgKappaSuspensionInverseSource_kills_generator
    (N : DGKappaCone R D J) (hN : N ∈ dgKappaConePerfectObjects R D J) :
    IsZeroVertex ((dgKappaSuspensionInverseSource R C D I J M hf).app
      (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex N)) := by
  let x := hf.choose.inv.app (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex N)
  obtain ⟨L, hL⟩ := DGNerve.Simplex.vertexEquiv.symm.surjective x
  change DGNerve.Simplex.vertex L = x at hL
  have h := hf.choose.invHomIso.app (DGNerve.Simplex.vertex N)
  change VertexIso ((dgNerve.map M.cone).app (Opposite.op ⦋0⦌) x)
    (DGNerve.Simplex.vertex N) at h
  rw [← hL, dgFunctorNerve_vertex] at h
  have hp := hr L ((dgKappaConePerfectObjects_iff_of_vertexIso R D J h).mpr hN)
  have hz := resolvedDGQuotientFunctor_kills R (DGKappaCone R C I)
    (dgKappaConePerfectObjects R C I) ⟨L, hp⟩
  change IsZeroVertex ((dgKappaSuspensionProjection R C I).app (Opposite.op ⦋0⦌) x)
  rw [← hL]
  exact hz

include hr in
/-- 同じ逆源関手は、元の perfect 集合の実安定閉包の全頂点を零化する。 -/
theorem dgKappaSuspensionInverseSource_kills :
    ∀ x ∈ Set.range ((dgStableClosureInclusion R (DGKappaCone R D J)
      (dgKappaConePerfectObjects R D J)).app (Opposite.op ⦋0⦌)),
      IsZeroVertex ((dgKappaSuspensionInverseSource R C D I J M hf).app
        (Opposite.op ⦋0⦌) x) := by
  let : IsExactFunctor (dgKappaSuspensionInverseSource R C D I J M hf) :=
    dgKappaSuspensionInverseSource_isExact R C D I J M hf
  rintro _ ⟨z, rfl⟩
  exact dgStableClosureInclusion_kills R (DGKappaCone R D J)
    (dgKappaConePerfectObjects R D J) (dgKappaSuspensionInverseSource R C D I J M hf)
    (dgKappaSuspensionInverseSource_kills_generator R C D I J M hf hr) z

/-- 元の実商の普遍性で下降した、同じ指定 cone 逆作用。 -/
def dgKappaSuspensionInverseMap :=
  dgKappaSuspensionDesc R D J (dgKappaSuspensionInfinity R C I)
    (dgKappaSuspensionInverseSource R C D I J M hf)
    (dgKappaSuspensionInverseSource_isExact R C D I J M hf)
    (dgKappaSuspensionInverseSource_kills R C D I J M hf hr)

theorem dgKappaSuspensionInverseMap_isExact :
    IsExactFunctor (dgKappaSuspensionInverseMap R C D I J M hf hr) :=
  dgKappaSuspensionDesc_isExact R D J _ _ _ _

/-- 同じ下降の余単位は、元の cone 同値の逆と元の実商射を回収する。 -/
def dgKappaSuspensionInverseMap_facIso :
    FunctorIso (dgKappaSuspensionProjection R D J ≫ dgKappaSuspensionInverseMap R C D I J M hf hr)
      (hf.choose.inv ≫ dgKappaSuspensionProjection R C I) :=
  dgKappaSuspensionDesc_facIso R D J _ _ _ _

end SerrePositivity.KST.NonConnective
