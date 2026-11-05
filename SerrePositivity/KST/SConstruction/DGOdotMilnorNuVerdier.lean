module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuKernel
public import SerrePositivity.InfinityCategories.Derived.SourceEquivalencePrecomposition
public import SerrePositivity.InfinityCategories.F1B.Localization.UniversalConsequences
public import SerrePositivity.InfinityCategories.F1B.Localization.PrecompositionCriterion

/-!
概要：同じ固定 ν 核包含と native resolved 商を指定完備化付き列へ接続する。
方針：native 列の全関手圏の普遍性を指定同値で輸送し、既構成の c を合成する。
規約：固定 ν 商辺には strict 局所化を要求せず、全比較で回収する。
使われ方：d④ の実零化面の同じ二辺と Cat^perf 列の照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : DGGluingMilnorSquare R d)
local instance : IsDGPretriangulated R (DGOdotGluing R d) :=
  dgGluingMilnor_isDGPretriangulated R d
local notation "n" => dgOdotMilnorCellNativeSequence R d
local notation "i" => dgOdotMilnorFlatKernelExactMap R d
local notation "q" => dgOdotMilnorNuNativeProjection R d
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "T" => dgKInputStableValue R (dgOdotMilnorCellInput R d)
local notation "U" => dgOdotMilnorSourceKernelNativeValueEquivalence R d h
local notation "V" => dgOdotMilnorCellMiddleNativeValueEquivalence R d

include h in
/-- 概要：同じ native resolved 商への固定 ν 射影は核の cofiber 辺の実局所化。
方針：Sp 正本の全関手圏の延長判定と同じ native 商の普遍性を使用する。
規約：局所化の一般補題を新設しない。使われ方：固定 ν 核列の商欄。 -/
lemma dgOdotMilnorNuKernelLocalization : IsLocalization (q).hom
    (cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (i))) := by
  letI := (q).isExact
  letI : IsExactFunctor (V).hom := isExactFunctor_of_isQCatEquivalence (V).isQCatEquivalence
  have hq := (n).isVerdier.quotient
  apply isLocalization_of_fullyFaithful_extensions
  · exact inverts_cofiberLocalizingEdges_of_kills _ _
      (fun b hb => (dgOdotMilnorNuKernel R d h b).2 hb)
  · intro Y hY
    exact precomposition_isFullyFaithful_of_sourceEquivalence (V)
      (n).projection.hom (hq.precomposition_isFullyFaithful Y)
  · intro Y hY F hF
    have hi : InvertsEdges ((V).hom ≫ F)
        (cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (n).inclusion)) := by
      intro a ha
      obtain ⟨s, z, hz, ⟨v⟩⟩ := ha
      have hm : (V).hom.app (Opposite.op ⦋1⦌) a ∈
          cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (i)) := by
        let t : CofiberSquare (edgeOfSimplex ((V).hom.app (Opposite.op ⦋1⦌) a)) := {
          toZeroTriangle := (s.map (V).hom).toZeroTriangle
          bottom_edge := (s.map (V).hom).bottom_edge
          isPushout := (s.map (V).hom).isPushout }
        refine ⟨t, (V).hom.app (Opposite.op ⦋0⦌) z, ?_, ⟨v.map (V).hom⟩⟩
        obtain ⟨x, ⟨w⟩⟩ := hz
        exact ⟨(U).hom.app (Opposite.op ⦋0⦌) x,
          ⟨((dgOdotMilnorFlatKernelNuComparison R d h).app x).trans (w.map (V).hom)⟩⟩
      exact (isInvertibleEdge_congr
        (e := (edgeOfSimplex ((V).hom.app (Opposite.op ⦋1⦌) a)).map ((truncation 2).map F))
        (f := (edgeOfSimplex a).map ((truncation 2).map ((V).hom ≫ F))) rfl).mp (hF hm)
    obtain ⟨G, ⟨v⟩⟩ := hq.exists_extension ((V).hom ≫ F) hi
    exact ⟨G, ⟨extensionIsoOfSourceEquivalence (V) (n).projection.hom F G v⟩⟩

/-- 概要：同じ固定 ν の実核包含と native resolved 商の Verdier 列。
方針：充満忠実性・thick 核・同じ実局所化を束ねる。
規約：完備化前の native 商を保つ。使われ方：実零化面の同じ二辺の認証。 -/
def dgOdotMilnorNuNativeSequence : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.{u + 1} where
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.left := K
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.middle := T
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.right := dgGluingMilnorNativeResolvedQuotient R d
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.inclusion := i
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.projection := q
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.isVerdier := ⟨dgOdotMilnorNuKernelInclusion_fullyFaithful R d h,
    dgOdotMilnorNuKernel R d h, dgOdotMilnorNuKernelLocalization R d h⟩

/-- 概要：同じ固定 ν 核列は D-21 の同じ c・hc で Cat^perf 列になる。
方針：既証明の固定 ν 完備性と実完備化を使用する。
規約：包含は元の ν 辺そのもの。使われ方：実零化面の完備化付き認証。 -/
def dgOdotMilnorNuPerfectSequence : PerfectVerdierSequence.{u + 1} where
  verdier := dgOdotMilnorNuNativeSequence R d h
  left_complete := dgKInputStableValue_isIdempotentComplete R _
  middle_complete := dgKInputStableValue_isIdempotentComplete R _
  right := dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
  completion := dgOdotMilnorCompletion R d
  isCompletion := dgOdotMilnorCompletion_isIdempotentCompletion R d

/-- 概要：同じ完備化後の列の右射は実固定 ν cell 商辺と全自然に比較できる。
方針：実二辺比較と中央同値の指定単位二胞体を合成する。
規約：同じ実 c と指定した全関手同型を保持する。使われ方：実面の右境界比較。 -/
def dgOdotMilnorNuPerfectProjectionComparison : FunctorIso
    (dgOdotMilnorCellProjectionExactMap R d).hom
    (dgOdotMilnorNuPerfectSequence R d h).projection.hom := by
  let a := (dgOdotMilnorCellProjectionExactMap R d).hom
  have e : FunctorIso a ((V).inv ≫ ((V).hom ≫ a)) := by
    simpa only [FunctorIso, Category.assoc, Category.id_comp] using
      ((V).invHomIso.postcomp a).symm
  have p := e.trans ((dgOdotMilnorCellProjectionNuComparison R d).precomp (V).inv)
  change FunctorIso a (((V).inv ≫ (dgOdotMilnorCellNativeProjection R d).hom) ≫
    (dgOdotMilnorCompletion R d).hom)
  exact (Category.assoc (V).inv (dgOdotMilnorCellNativeProjection R d).hom
    (dgOdotMilnorCompletion R d).hom).symm ▸ p

end SerrePositivity.KST.SConstruction
