module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCellNuComparison
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulIso

/-!
概要：同じ固定 ν 核包含と native resolved 商への実射影の核を照合する。
方針：構成済みの native 頂点同値と二辺の全関手比較を使用する。
規約：固定 ν 射影を strict 商とせず、native 商を経由する射を区別する。
使われ方：実零化面に対応する固定 ν の完備化付き列。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : DGGluingMilnorSquare R d)
local notation "A" => dgOdotMilnorCellKernelCategory R d
local notation "B" => dgOdotMilnorCellMiddleCategory R d
local notation "i" => dgOdotMilnorCellKernelInclusion R d
local notation "q" => dgOdotMilnorCellNativeProjection R d
local notation "G" => DGOdotGluing R d
local notation "P" => dgQuotientImage R
  (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "T" => dgKInputStableValue R (dgOdotMilnorCellInput R d)
local notation "U" => dgOdotMilnorSourceKernelNativeValueEquivalence R d h
local notation "V" => dgOdotMilnorCellMiddleNativeValueEquivalence R d
local notation "j" => dgOdotMilnorFlatKernelExactMap R d

local instance : IsDGPretriangulated R (DGOdotGluing R d) :=
  dgGluingMilnor_isDGPretriangulated R d
local instance : IsDGPretriangulated R (DGCategoryCellResolution.Source R (G)) :=
  dgCellResolutionSource_isDGPretriangulated R (G)

/-- 概要：固定 ν の cell 値から同じ native resolved 商へ向かう実完全射。
方針：同じ native 頂点同値の逆と元の strict 商を合成する。
規約：固定 ν の完備化後の商射影と区別する。使われ方：完備化付き実列の商。 -/
def dgOdotMilnorNuNativeProjection : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (T) (dgGluingMilnorNativeResolvedQuotient R d) where
  hom := (V).inv ≫ resolvedDGQuotientProjection R (G) (P)
  isExact := by
    letI : IsExactFunctor (V).inv :=
      isExactFunctor_of_isQCatEquivalence (V).symm.isQCatEquivalence
    letI : IsExactFunctor (resolvedDGQuotientProjection R (G) (P)) :=
      dgQuotientNerveProjection_isExactFunctor R _ _ (resolvedDGQuotient_localKFlat R (G) (P))
    exact isExactFunctor_comp (V).inv (resolvedDGQuotientProjection R (G) (P))

/-- 概要：同じ固定 ν 核包含は native 包含を両頂点同値で運んだものと全自然に同型。
方針：構成済み二辺比較と指定単位二胞体を合成する。
規約：元の固定 ν 包含を保つ。使われ方：充満忠実性と核像の照合。 -/
def dgOdotMilnorNuKernelInclusionComparison : FunctorIso (j).hom
    ((U).inv ≫ ((i).hom ≫ (V).hom)) := by
  have a : FunctorIso (j).hom ((U).inv ≫ ((U).hom ≫ (j).hom)) := by
    simpa only [FunctorIso, Category.assoc, Category.id_comp] using
      ((U).invHomIso.postcomp (j).hom).symm
  exact a.trans ((dgOdotMilnorFlatKernelNuComparison R d h).precomp (U).inv)

include h in
/-- 概要：同じ固定 ν 核包含は充満忠実。
方針：元の native 包含の充満忠実性を両頂点同値と指定全比較で移す。
規約：Milnor 条件を明示する。使われ方：固定 ν の実列の第一欄。 -/
lemma dgOdotMilnorNuKernelInclusion_fullyFaithful : IsFullyFaithful (j).hom :=
  (dgOdotMilnorNuKernelInclusionComparison R d h).isFullyFaithful_iff.mpr
    ((U).symm.isQCatEquivalence.isFullyFaithful.comp
      ((dgOdotMilnorCellNativeSequence R d).isVerdier.fullyFaithful.comp
        (V).isQCatEquivalence.isFullyFaithful))

include h in
/-- 概要：同じ native resolved 商への射影の零対象核は固定 ν 核包含の本質像。
方針：native の同じ thick 核を両指定頂点同値で輸送する。
規約：retract を含む同じ実核を保持する。使われ方：固定 ν の実列の核欄。 -/
lemma dgOdotMilnorNuKernel (b : (T).obj _⦋0⦌) :
    IsZeroVertex ((dgOdotMilnorNuNativeProjection R d).hom.app (Opposite.op ⦋0⦌) b) ↔
      b ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (j) := by
  change IsZeroVertex ((resolvedDGQuotientProjection R (G) (P)).app (Opposite.op ⦋0⦌)
    ((V).inv.app (Opposite.op ⦋0⦌) b)) ↔ _
  rw [resolvedDGQuotientProjection_zero_iff_thickEssentialImage R (G) (P)]
  constructor
  · rintro ⟨a, ⟨v⟩⟩
    refine ⟨(U).hom.app (Opposite.op ⦋0⦌) a, ?_⟩
    exact ⟨((dgOdotMilnorFlatKernelNuComparison R d h).app a).trans
      ((v.map (V).hom).trans ((V).invHomIso.app b))⟩
  · rintro ⟨a, ⟨v⟩⟩
    refine ⟨(U).inv.app (Opposite.op ⦋0⦌) a, ?_⟩
    let w := ((dgOdotMilnorNuKernelInclusionComparison R d h).app a).symm.trans v
    exact ⟨((V).homInvIso.app ((i).hom.app (Opposite.op ⦋0⦌)
      ((U).inv.app (Opposite.op ⦋0⦌) a))).symm.trans (VertexIso.map w (V).inv)⟩

end SerrePositivity.KST.SConstruction
