module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput

/-!
概要：同じ実平坦懸垂の Verdier 普遍性から、指定零化完全関手の実下降を回収する。
方針：元の全零化完全関手圏の同値の実逆を使い、前合成比較を全関手同型で保持する。
規約：対象別の下降を構成する。全 dg 入力作用や厳密 dg 商射とは同一視しない。
使われ方：K-7 d4・e の実模型比較を同じ実商へ下降する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
local notation "C" => dgNerve R (DGKappaCone R D I)
local notation "Q" => dgKappaSuspensionInfinity R D I
local notation "i" => dgStableClosureInclusion R (DGKappaCone R D I)
  (dgKappaConePerfectObjects R D I)
local notation "q" => dgKappaSuspensionProjection R D I
local instance descentConeStable : IsStable C := dgNerve_isStable_of_pretriangulated R _
local instance descentKernelStable : IsStable
    (dgStableClosureNerve R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) :=
  dgStableClosureNerve_isStable R _ _
local instance descentSuspensionStable : IsStable Q := dgKappaSuspensionInfinity_isStable R D I
local instance descentProjectionExact : IsExactFunctor q :=
  (dgKappaSuspension_isStableVerdierSequence R D I).quotientExact

variable (Y : SSet.{max (u + 1) v}) [Quasicategory Y] [IsStable Y]

/-- 同じ実懸垂射による、全零化完全関手圏への指定前合成同値。 -/
def dgKappaSuspensionDescentEquivalence :=
  ((dgKappaSuspension_isStableVerdierSequence R D I).universal Y).choose

variable (F : dgNerve R (DGKappaCone R D I) ⟶ Y) (hF : IsExactFunctor F)
  (hK : ∀ x ∈ Set.range ((dgStableClosureInclusion R (DGKappaCone R D I)
    (dgKappaConePerfectObjects R D I)).app (Opposite.op ⦋0⦌)),
    IsZeroVertex (F.app (Opposite.op ⦋0⦌) x))

/-- 元の指定関手を表す、同じ全零化完全関手圏の頂点。 -/
def dgKappaSuspensionDescentInputVertex :
    (zeroingExactFunctors C Y (Set.range ((i).app (Opposite.op ⦋0⦌))) : SSet) _⦋0⦌ :=
  ⟨functorVertex F, by
    intro α
    rw [SimplexCategory.hom_zero_zero α]
    simp only [op_id, Functor.map_id_apply]
    exact (isZeroingExactFunctorVertex_functorVertex _ _ _ F).mpr ⟨hF, hK⟩⟩

/-- 同じ前合成同値の実逆が選ぶ、下降関手の元の完全関手頂点。 -/
def dgKappaSuspensionDescentVertex :=
  (dgKappaSuspensionDescentEquivalence R D I Y).inv.app (Opposite.op ⦋0⦌)
    (dgKappaSuspensionDescentInputVertex R D I Y F hF hK)

/-- 同じ実商からの実下降関手。 -/
def dgKappaSuspensionDesc : Q ⟶ Y :=
  (functorVertexEquiv Q Y).symm (dgKappaSuspensionDescentVertex R D I Y F hF hK).val

theorem dgKappaSuspensionDesc_isExact : IsExactFunctor
    (dgKappaSuspensionDesc R D I Y F hF hK) :=
  fullSubcomplexOnVertices_vertex (dgKappaSuspensionDescentVertex R D I Y F hF hK)

/-- 下降の前合成比較は、元の全零化関手圏の同値の余単位そのものから回収する。 -/
def dgKappaSuspensionDesc_facIso :
    FunctorIso (q ≫ dgKappaSuspensionDesc R D I Y F hF hK) F := by
  have e := VertexIso.map
    ((dgKappaSuspensionDescentEquivalence R D I Y).invHomIso.app
      (dgKappaSuspensionDescentInputVertex R D I Y F hF hK))
    (zeroingExactFunctors C Y (Set.range ((i).app (Opposite.op ⦋0⦌)))).ι
  have hv : functorVertex (dgKappaSuspensionDesc R D I Y F hF hK) =
      (dgKappaSuspensionDescentVertex R D I Y F hF hK).val :=
    (functorVertexEquiv Q Y).apply_symm_apply _
  change VertexIso (((pre q).app Y).app (Opposite.op ⦋0⦌)
    (dgKappaSuspensionDescentVertex R D I Y F hF hK).val) (functorVertex F) at e
  rw [← hv] at e
  exact e

/-- 同じ実商からの完全関手の比較は、元の実商射への前合成から反映できる。 -/
def dgKappaSuspensionFunctorIso_of_precomp (F G : Q ⟶ Y)
    (hF : IsExactFunctor F) (hG : IsExactFunctor G) (e : FunctorIso (q ≫ F) (q ≫ G)) :
    FunctorIso F G := by
  let x : (exactFunctors Q Y : SSet) _⦋0⦌ := ⟨functorVertex F, by
    intro α
    rw [SimplexCategory.hom_zero_zero α]
    simp only [op_id, Functor.map_id_apply]
    exact (isExactFunctorVertex_functorVertex _ _ F).mpr hF⟩
  let y : (exactFunctors Q Y : SSet) _⦋0⦌ := ⟨functorVertex G, by
    intro α
    rw [SimplexCategory.hom_zero_zero α]
    simp only [op_id, Functor.map_id_apply]
    exact (isExactFunctorVertex_functorVertex _ _ G).mpr hG⟩
  let U := dgKappaSuspensionDescentEquivalence R D I Y
  have e' : VertexIso (U.hom.app (Opposite.op ⦋0⦌) x) (U.hom.app (Opposite.op ⦋0⦌) y) :=
    (isFullyFaithful_fullSubcomplexOnVertices_ι _
      (IsZeroingExactFunctorVertex C Y (Set.range ((i).app (Opposite.op ⦋0⦌))))).preimageVertexIso e
  exact VertexIso.map (U.isFullyFaithful.preimageVertexIso e') (exactFunctors Q Y).ι

end SerrePositivity.KST.NonConnective
