module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientPullback

/-! # 元の Cat^perf 比較正方形と不変量値の四頂点
概要：指定比較道を持つ正方形の四角を、元の左端・lax 圏・完備化先へ照合する。
方針：同じ全単体の持ち上げの頂点を回収し、同じ不変量の零単体作用を使う。
規約：頂点を同値な代用対象へ先に替えない。使われ方：実 BF 積への全図式の移送。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)

/-- Cat^perf 正方形の左下は元の左端。 -/
lemma universalSquare_vertex00 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalSquare 0 0 =
    perfectStableVertex d.left d.left_complete := by
  apply Subtype.ext
  exact d.universalRawSquare_vertices.1

/-- Cat^perf 正方形の右下は元の lax pullback。 -/
lemma universalSquare_vertex10 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalSquare 1 0 =
    perfectLaxVertex p q d.c_complete d.d_complete := by
  apply Subtype.ext
  exact d.universalRawSquare_vertices.2.1

/-- Cat^perf 正方形の右上は元の完備化先の恒等 lax pullback。 -/
lemma universalSquare_vertex11 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalSquare 1 1 =
    perfectLaxVertex (𝟙 d.sequence.right) (𝟙 d.sequence.right)
      d.sequence.right_complete d.sequence.right_complete := by
  apply Subtype.ext
  exact d.universalRawSquare_vertices.2.2.1

/-- Cat^perf 正方形の左上は元の実商の完備化先。 -/
lemma universalSquare_vertex01 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalSquare 0 1 =
    d.sequence.rightVertex := by
  apply Subtype.ext
  exact d.universalRawSquare_vertices.2.2.2

variable (F : perfectStableInfinity.{u} ⟶ Sp.{u})

/-- 同じ Sp 正方形の左下は元の左端の同じ値。 -/
lemma universalValueSquare_vertex00 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.universalValueSquare F) 0 0 =
    F.app (Opposite.op ⦋0⦌) (perfectStableVertex d.left d.left_complete) :=
  congrArg (fun x => F.app (Opposite.op ⦋0⦌) x) d.universalSquare_vertex00

/-- 同じ Sp 正方形の右下は元の lax pullback の同じ値。 -/
lemma universalValueSquare_vertex10 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.universalValueSquare F) 1 0 =
    F.app (Opposite.op ⦋0⦌) (perfectLaxVertex p q d.c_complete d.d_complete) :=
  congrArg (fun x => F.app (Opposite.op ⦋0⦌) x) d.universalSquare_vertex10

/-- 同じ Sp 正方形の右上は元の恒等 lax pullback の同じ値。 -/
lemma universalValueSquare_vertex11 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.universalValueSquare F) 1 1 =
    F.app (Opposite.op ⦋0⦌) (perfectLaxVertex (𝟙 d.sequence.right) (𝟙 d.sequence.right)
      d.sequence.right_complete d.sequence.right_complete) :=
  congrArg (fun x => F.app (Opposite.op ⦋0⦌) x) d.universalSquare_vertex11

/-- 同じ Sp 正方形の左上は元の商の完備化先の同じ値。 -/
lemma universalValueSquare_vertex01 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.universalValueSquare F) 0 1 =
    F.app (Opposite.op ⦋0⦌) d.sequence.rightVertex :=
  congrArg (fun x => F.app (Opposite.op ⦋0⦌) x) d.universalSquare_vertex01

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
