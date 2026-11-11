module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceNuRoof
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNativePerfect
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedQuasiEquivalenceForward

/-!
概要：増大屋根の同じ cell 始域・thick 平坦核の native 完備性を充足する。
方針：元小 Perf と cell 増大の同値、同じ厳密核比較の準同値で輸送する。
規約：核を Perf 値へ置換せず、同じ対象集合と同じ比較関手を保持する。
使われ方：実零化面の Cat^perf 認証に使う左端・中央の native 証拠。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d))
local notation "T" => DGCategoryCellResolution.Source R (A)
local notation "B" => DGOdotGluing R d
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R (B)
  (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)))

/-- 概要：元対角始域の同じ cell 分解の coherent 冪等完備性。
方針：元小 Perf の完備性を実 cell 増大同値で戻す。
規約：Milnor 条件を要しない。使われ方：始域比較屋根の native 左端。 -/
lemma dgOdotMilnorSourceCell_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (T)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d).of_equivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (A)).symm

/-- 概要：同じ thick 平坦核の coherent 冪等完備性。
方針：実 cell 始域からの同じ比較同値で輸送する。
規約：Milnor 条件を明示する。使われ方：実零化面の native 左端の証拠。 -/
lemma dgOdotMilnorSourceKernel_complete (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (K)) :=
  (dgOdotMilnorSourceCell_complete R d).of_equivalence
    (dgOdotMilnorSourceKernelNerve_isQCatEquivalence R d h).choose

/-- 概要：元 gluing の同じ cell 分解の coherent 冪等完備性。
方針：元 gluing の完備性を実 cell 増大同値で戻す。
規約：商への射影を変更しない。使われ方：実零化面の native 中央の証拠。 -/
lemma dgOdotMilnorCellMiddle_complete :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGCategoryCellResolution.Source R (B))) :=
  (dgOdotMilnorNativeMiddle_complete R d).of_equivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (B)).symm

/-- 概要：同じ thick 平坦核自身の dg 前三角性。
方針：元始域の cell 分解の前三角性を同じ厳密準同値で輸送する。
規約：native 安定性だけで前三角性を代用しない。使われ方：D-21 の核への特殊化。 -/
lemma dgOdotMilnorSourceKernel_isDGPretriangulated (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (K) := by
  letI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (A) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSource_isDGPretriangulated R d
  letI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (T) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (A)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence_forward R (T) (K)
    (dgOdotMilnorSourceKernelDGMap R d)
    (dgOdotMilnorSourceKernelDGMap_quasiEquivalence R d h)

end SerrePositivity.KST.SConstruction
