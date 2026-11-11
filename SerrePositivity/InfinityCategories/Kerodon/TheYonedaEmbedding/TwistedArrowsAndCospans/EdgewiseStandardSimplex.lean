module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
概要：edgewise subdivision の単体を次数が二倍の標準単体からの射として表示する。
方針：左因子の反転同型と join の標準単体同型を合成し、Yoneda の同値を適用する。
規約：次数は n+n+1 と記す。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、Corollary 5.6.0.6（Tag 028T）、反転比較の充填問題の有限単体表示。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：edgewise の n 次の重みは標準 (n+n+1) 単体と同型。
方針：反転した左標準単体を元へ戻し、二つの標準単体の join の同型を使う。
規約：同型の定義に充填性は要求しない。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、ホーンの像の標準単体内での計算。 -/
def edgewiseWeightIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.obj ⦋n⦌ ≅ (Δ[n + n + 1] : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (stdSimplex.opIso ⦋n⦌) (Iso.refl Δ[n]) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n n

/-- 概要：edgewise subdivision の n 単体と元の (n+n+1) 単体の全単射。
方針：重みの標準単体同型で射の始域を変え、Yoneda の同値を使う。
規約：全単射は全ての単体集合 X に対して定義する。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、射影の充填問題を X の単体へ戻す。 -/
def edgewiseSimplexEquiv (X : SSet.{u}) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) _⦋n⦌ ≃ X _⦋n + n + 1⦌ :=
  (Iso.homCongr (edgewiseWeightIso n) (Iso.refl X)).trans SSet.yonedaEquiv

/-- 概要：edgewise の単体の標準単体表示は標的への後合成について自然。
方針：始域の同型の逆による前合成と Yoneda の同値を計算する。
規約：X と Y の Kan 性は不要。
使われ方：Kerodon Remark 8.1.1.4（Tag 00B3）、図式全体で自然な標準単体表示。 -/
lemma edgewiseSimplexEquiv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) _⦋n⦌) :
    edgewiseSimplexEquiv Y n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f).app (Opposite.op ⦋n⦌) s) =
      f.app (Opposite.op ⦋n + n + 1⦌) (edgewiseSimplexEquiv X n s) := by
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
