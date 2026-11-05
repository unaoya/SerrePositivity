module
public import SerrePositivity.InfinityCategories.Derived.DGTotalQuotientPerfectVerticesZero
public import SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagrams
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability
/-!
概要：任意の小さい dg 圏の全対象商の Perf は零の安定 ∞ 圏である。
方針：native 全頂点の零性を安定圏として束ね、実 ∞ 圏同値を通じて任意の Perf 模型へ輸送する。
規約：K-B・S 構成本体を import せず、IsZeroCategory は Sp 正本を使用する。
使われ方：D-20。Sp-6 s2 の A/A の Perf 零像と presentedPerfectDGNerve への比較。
-/
@[expose] public section
noncomputable section
universe u v
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
open SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 全対象商の実 Perf nerve を持つ安定圏。 -/
def dgTotalQuotientPerfectStableCategory : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max (u + 1) v} where
  obj := dgModulePerfectInfinityCategory R (DGQuotient.QuotientObject D Set.univ)
  isQuasicategory := inferInstance
  isStable := dgModulePerfectInfinityCategory_isStable R _

/-- 全対象商の実 Perf は零の安定圏。 -/
theorem dgTotalQuotientPerfect_isZero :
    _root_.SerrePositivity.InfinityCategories.Stable.Infinity.IsZeroCategory (dgTotalQuotientPerfectStableCategory R D) :=
  dgTotalQuotientPerfect_vertex_isZero R D

/-- 元の実 Perf との同値により、小模型・ラベル付き模型の零性を回収する。 -/
theorem dgTotalQuotientPerfect_isZero_of_equivalence
    (A : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max (u + 1) v})
    (e : QCatEquivalence A.obj
      (dgModulePerfectInfinityCategory R (DGQuotient.QuotientObject D Set.univ))) :
    _root_.SerrePositivity.InfinityCategories.Stable.Infinity.IsZeroCategory A := by
  let := dgModulePerfectInfinityCategory_isStable R (DGQuotient.QuotientObject D Set.univ)
  have h := isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  change IsExactFunctor e.inv at h
  let : IsExactFunctor e.inv := h
  intro z
  exact (IsExactFunctor.preservesZero (F := e.inv) _
    (dgTotalQuotientPerfect_vertex_isZero R D (e.hom.app _ z))).of_vertexIso
      (e.homInvIso.app z)

end SerrePositivity.InfinityCategories
