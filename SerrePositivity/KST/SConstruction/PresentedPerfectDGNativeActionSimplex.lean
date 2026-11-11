module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGRightTensorAction
public import SerrePositivity.KST.SConstruction.DGNerveTensorSimplex

/-! # native 関手族の全単体による実 Perf 右作用
概要：native 関手族とラベル付き Perf の単体へ、元の実 tensor 右作用を適用する。
方針：異なる対象宇宙を許す native tensor 比較に、元の右作用 dg 関手を後合成する。
規約：ラベル・関手族の因子順と全作用素を保持。使われ方：実単体的 Perf 作用。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]

/-- 元の dg 単体の関手作用は、異なる対象宇宙でも全引き戻しを保つ。 -/
lemma dgNativeSimplex_map_pullback {C : Type w} {B : Type v} [DGCategory A C] [DGCategory A B]
    {M N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A C N) (F : DGFunctor A C B)
    (α : Fin (M + 1) →o Fin (N + 1)) :
    (s.pullback α).map F = (s.map F).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback s.toSimplexData F α

/-- 元のラベル単体と native 関手族の単体に対する、全次数の実 Perf 右作用。 -/
def presentedPerfectDGNativeActionSimplex {N : ℕ}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (PresentedPerfectDGObject A D) N)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A D E) N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (PresentedPerfectDGObject A E) N :=
  (dgNerveTensorSimplex A x s).map (presentedPerfectDGRightTensorAction A D E)

/-- 元の実 Perf 右作用の全単体は、退化を含む全単体作用素と可換。 -/
lemma presentedPerfectDGNativeActionSimplex_pullback {M N : ℕ}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (PresentedPerfectDGObject A D) N)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A D E) N) (α : Fin (M + 1) →o Fin (N + 1)) :
    presentedPerfectDGNativeActionSimplex A D E (x.pullback α) (s.pullback α) =
      (presentedPerfectDGNativeActionSimplex A D E x s).pullback α := by
  unfold presentedPerfectDGNativeActionSimplex
  rw [dgNerveTensorSimplex_pullback]
  exact dgNativeSimplex_map_pullback A (dgNerveTensorSimplex A x s)
    (presentedPerfectDGRightTensorAction A D E) α

end SerrePositivity.KST.SConstruction
