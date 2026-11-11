module
public import SerrePositivity.KST.SConstruction.DGOdotLaxVerdierConnection
public import SerrePositivity.KST.SConstruction.DGOdotMorita
public import SerrePositivity.KST.SConstruction.DGKInputIdempotentComplete
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotient

/-!
概要：d の具体的二射を、実 ⊙ を終点とする Cat^perf の商入力へ接続する。
方針：c の同じ Morita 辺の逆を完全な完備化射とし、D の完備性を接続する。
規約：未供給の d 入力を証明済みと数えない。
使われ方：Tamme 分裂と Verdier 列から LT の Cat^perf 版を導く形式的接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants

open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：c の同じ ⊙→商辺を、順方向を固定した同値にする。
方針：既存の Morita 比較を使う。規約：辺を選び直さない。
使われ方：実 ⊙ を終点とする完備化射。 -/
def dgOdotQuotientNuEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotAlgebraInput R d)).obj
    (dgKInputStableValue R (dgOdotQuotientInputVertex R d)).obj :=
  (dgOdotInputNuMap_isQCatEquivalence R d).choose

/-- 概要：商から元の実 ⊙ の ν 値への完全射。
方針：指定 Morita 辺の同じ逆を使う。規約：一般の商完備化を構成しない。
使われ方：Cat^perf 版 LT の終点を固定する。 -/
def dgOdotQuotientCompletion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotQuotientInputVertex R d))
    (dgKInputStableValue R (dgOdotAlgebraInput R d)) :=
  ⟨(dgOdotQuotientNuEquivalence R d).inv,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotQuotientNuEquivalence R d).symm.isQCatEquivalence⟩

/-- 概要：完備化と元の Morita 辺の合成は元の ⊙ の恒等へ戻る。
方針：同じ同値の指定二胞体を保持する。規約：厳密等号は要求しない。
使われ方：元の ⊙ を保つ比較三角形。 -/
def dgOdotQuotientCompletion_forward : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKInputNuMap R (dgOdotQuotientInputMap R d)).hom ≫
      (dgOdotQuotientCompletion R d).hom)
    (𝟙 (dgKInputStableValue R (dgOdotAlgebraInput R d)).obj) :=
  (dgOdotQuotientNuEquivalence R d).homInvIso

/-- 概要：逆順の合成も元の同じ商の恒等へ戻る。
方針：同じ同値のもう一つの二胞体を使う。規約：元の商を変更しない。
使われ方：c と e の実比較の整合。 -/
def dgOdotQuotientCompletion_backward : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotQuotientCompletion R d).hom ≫
      (dgKInputNuMap R (dgOdotQuotientInputMap R d)).hom)
    (𝟙 (dgKInputStableValue R (dgOdotQuotientInputVertex R d)).obj) :=
  (dgOdotQuotientNuEquivalence R d).invHomIso

/-- 概要：元の ⊙ の完備性があれば同じ逆射は実冪等完備化。
方針：同値の充満忠実性と本質的全射性を既存の retract 条件へ渡す。
規約：coherent 完備性の供給は明示入力。使われ方：Cat^perf の実列。 -/
lemma dgOdotQuotientCompletion_isCompletion
    (hO : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (dgKInputStableValue R (dgOdotAlgebraInput R d)).obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (dgOdotQuotientCompletion R d).hom := by
  refine ⟨hO, (dgOdotQuotientNuEquivalence R d).symm.isFullyFaithful, ?_⟩
  intro a
  obtain ⟨b, ⟨e⟩⟩ := (dgOdotQuotientNuEquivalence R d).symm.isEssentiallySurjective a
  exact ⟨b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso e.symm⟩

/-- 概要：Cat^perf に必要な元の四対象の完備性を分離する。
方針：全 coherent 冪等図式の条件を使う。規約：H⁰ 完備性との比較を自作しない。
使われ方：具体的供給後も同じ LT の形式的証明を使う入口。 -/
structure DGOdotCatPerfInput : Prop where
  source_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete
    (dgKInputStableValue R (dgOdotDiagonalSourceInput R d)).obj
  left_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (dgKInputStableValue R (dgOdotLeftInput R d)).obj
  right_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (dgKInputStableValue R (dgOdotRightInput R d)).obj
  odot_complete : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (dgKInputStableValue R (dgOdotAlgebraInput R d)).obj

/-- 概要：元の四対象の完備性証人を追加仮定なしに供給する。
方針：D の実 Perf 完備性を同じ固定 ν 値へ移す。
規約：D2・β3・S 内長方形はここで構成しない。使われ方：LT の標準入力。 -/
theorem dgOdotCatPerfInput : DGOdotCatPerfInput R d where
  source_complete := dgKInputStableValue_isIdempotentComplete R _
  left_complete := dgKInputStableValue_isIdempotentComplete R _
  right_complete := dgKInputStableValue_isIdempotentComplete R _
  odot_complete := dgKInputStableValue_isIdempotentComplete R _

namespace DGOdotCatPerfInput
variable {R d} (c : DGOdotCatPerfInput R d) (h : DGOdotLaxVerdierInput R d)

/-- 概要：d の同じ商列を実 ⊙ に完備化した Cat^perf の入力。
方針：c の Morita 逆と既存の商入力構造体を使う。
規約：商自体の完備性・完備化後の厳密商性は要求しない。
使われ方：Tamme 分裂から LT の実二脚の結論へ接続する。 -/
def perfectQuotient : PerfectLaxQuotient (dgOdotLowerExactMap R d)
    (dgOdotUpperExactMap R d) where
  left := dgKInputStableValue R (dgOdotDiagonalSourceInput R d)
  rawQuotient := dgKInputStableValue R (dgOdotQuotientInputVertex R d)
  right := dgKInputStableValue R (dgOdotAlgebraInput R d)
  inclusion := h.inclusion
  rawProjection := h.projection
  isVerdier := h.isVerdier
  left_complete := c.source_complete
  c_complete := c.left_complete
  d_complete := c.right_complete
  completion := dgOdotQuotientCompletion R d
  isCompletion := dgOdotQuotientCompletion_isCompletion R d c.odot_complete

/-- 概要：完備化後の元の商射を厳密に回収する。
方針：同じ入力の定義を読む。規約：別の商射を使わない。
使われ方：d の二射と LT の列の照合。 -/
lemma perfectQuotient_projection : (c.perfectQuotient h).sequence.projection.hom =
    h.projection.hom ≫ (dgOdotQuotientCompletion R d).hom := rfl

/-- 概要：終点は元の同じ実 ⊙ の安定値。
方針：入力した終点を保持する。規約：抽象的な完備化先へ置換しない。
使われ方：LT の右上対象の回収。 -/
lemma perfectQuotient_right : (c.perfectQuotient h).right =
    dgKInputStableValue R (dgOdotAlgebraInput R d) := rfl

end DGOdotCatPerfInput
end SerrePositivity.KST.SConstruction
