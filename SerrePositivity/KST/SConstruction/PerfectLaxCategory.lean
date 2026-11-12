module
public import SerrePositivity.KST.SConstruction.PerfectLaxIdempotent
public import SerrePositivity.KST.SConstruction.PerfectSemiorthogonalSplitInfinity
public import SerrePositivity.KST.LocalizingInvariants.LaxSemiorthogonal

/-! # 元の lax pullback の Cat^perf 頂点と半直交分解
概要：同じ実 lax pullback を Cat^perf に束ね、元の包含・右包含・第一射影を保持する。
方針：証明済みの coherent 冪等完備性と F2 の元の安定性・半直交分解を使う。
規約：lax pullback を別の完備化へ置換しない。使われ方：Tamme の分裂の具体的入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete D.obj)

include hC hD in
/-- 元の F2 lax pullback そのものは、全 coherent 冪等図式について冪等完備。 -/
lemma perfectLaxCategory_isIdempotentComplete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (laxCategory p q).obj :=
  perfectLaxPullback_isIdempotentComplete p.hom q.hom hC hD

/-- 元の同じ実 lax pullback を Cat^perf の頂点にする。 -/
def perfectLaxVertex : perfectStableInfinity.{u} _⦋0⦌ :=
  perfectStableVertex (laxCategory p q) (perfectLaxCategory_isIdempotentComplete p q hC hD)

/-- Cat^perf の元の lax pullback 頂点は、同じ実安定圏を回収する。 -/
lemma perfectStableObject_laxVertex :
    perfectStableObject (perfectLaxVertex p q hC hD) = laxCategory p q := rfl

/-- 同じ元の lax pullback の、元の全単体上の半直交分解。 -/
def perfectLaxSemiorthogonal :
    PerfectSemiorthogonalDecomposition (perfectStableVertex D hD) (perfectStableVertex C hC)
      (perfectLaxVertex p q hC hD) :=
  laxSemiorthogonal p q

/-- 左包含は同じ元の D からの完全関手。 -/
lemma perfectLaxSemiorthogonal_inclusion :
    (perfectLaxSemiorthogonal p q hC hD).inclusion = LaxInclusion.exactFromD p q := rfl

/-- 右包含は同じ元の C からの完全関手。 -/
lemma perfectLaxSemiorthogonal_rightInclusion :
    (perfectLaxSemiorthogonal p q hC hD).rightInclusion = LaxInclusion.exactFromC p q := rfl

/-- 商の射影は F2 の元の第一射影そのもの。 -/
lemma perfectLaxSemiorthogonal_projection :
    (perfectLaxSemiorthogonal p q hC hD).projection = laxFst p q := rfl

end SerrePositivity.KST.SConstruction
