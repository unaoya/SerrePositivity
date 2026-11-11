module
public import SerrePositivity.KST.SConstruction.DGKInputIdempotentComplete
public import SerrePositivity.KST.SConstruction.PerfectStableInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices

/-!
概要：同じ固定 S・ν を Cat^perf へ全単体を保って持ち上げる。
方針：D の実 Perf 完備性と既存の全部分複体持ち上げを使う。
規約：入力・辺・高次作用を選び直さない。使われ方：Cat^perf 不変量の固定 S への制限。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R]

/-- 概要：固定 ν の全頂点は Cat^perf の頂点条件を満たす。
方針：入力頂点を元の厳密 dg 対象で表示する。
規約：全入力に適用する。使われ方：同じ ν の全部分複体への持ち上げ。 -/
lemma dgKInputNu_vertex_complete (x : (dgKInputInfinity.{u, v} R) _⦋0⦌) :
    perfectStableVertexPredicate ((dgKInputNu R).app (Opposite.op ⦋0⦌) x) := by
  obtain ⟨P, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv (PerfDGInput.{u, v} R)).surjective x
  change perfectStableVertexPredicate
    ((dgKInputNu R).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P))
  rw [dgKInputNu_vertex]
  exact dgKInputStableValue_isIdempotentComplete R P

/-- 概要：固定 ν の Cat^perf 値への同じ全単体の持ち上げ。
方針：全部分複体の既存構成を使う。規約：対象別定義だけで代用しない。
使われ方：任意の Cat^perf 不変量を同じ S 上で評価する。 -/
def dgKInputPerfectNu : dgKInputInfinity.{u, v} R ⟶
    perfectStableInfinity.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift perfectStableVertexPredicate (dgKInputNu R)
    (dgKInputNu_vertex_complete R)

/-- 概要：包含後は元の固定 ν と全単体で厳密に一致する。
方針：全部分複体の包含則。規約：自然同値に弱めない。
使われ方：既存の相対入力と同じ ν を照合する。 -/
lemma dgKInputPerfectNu_inclusion :
    dgKInputPerfectNu.{u, v} R ≫ perfectStableInfinityInclusion = dgKInputNu R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：持ち上げた頂点は元の同じ実安定値。
方針：包含の単射性と固定 ν の頂点式を使う。
規約：完備性証人のみを加える。使われ方：LT の元の四頂点との照合。 -/
lemma dgKInputPerfectNu_vertex (P : PerfDGInput.{u, v} R) :
    (dgKInputPerfectNu R).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P) =
      perfectStableVertex (dgKInputStableValue R P)
        (dgKInputStableValue_isIdempotentComplete R P) := by
  apply Subtype.ext
  exact dgKInputNu_vertex R P

end SerrePositivity.KST.SConstruction
