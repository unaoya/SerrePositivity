module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.EdgewiseVertexFiberLift
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TwistedArrowSourceLift

/-!
概要：大域的に固定した twisted arrow の持ち上げを、元の恒等射上の fiber 全体へ制限する。
方針：恒等点と fiber 包含で終点の引き戻しへ入り、同じ切断を使う。
規約：新しい点ごとの切断は選ばない。同じ fiber の右端は恒等写像。
使われ方：大域評価の恒等点上の作用の同値性。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (b : B _⦋0⦌)

/-- 元の恒等射と同じ fiber の全終点を、元の終点の引き戻しへ入れる。 -/
def twistedIdentityFiberInclusion : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight B) p :=
  pullback.lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseIdentityPoint b)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (by
    rw [SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseIdentityPoint_right, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp])

/-- 元の大域切断を、同じ恒等射上の全 fiber パラメータへ制限する。 -/
def twistedIdentityFiberFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision E :=
  twistedIdentityFiberInclusion p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowRightSection p

/-- 同じ制限した全族の底は、元の恒等点に厳密に定値。 -/
lemma twistedIdentityFiberFamily_base :
    twistedIdentityFiberFamily p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap p =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseIdentityPoint b) := by
  rw [twistedIdentityFiberFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowRightSection_map,
    twistedIdentityFiberInclusion, pullback.lift_fst]

/-- 同じ制限した全族の右端は、元の fiber の包含そのもの。 -/
lemma twistedIdentityFiberFamily_right :
    twistedIdentityFiberFamily p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight E = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  rw [twistedIdentityFiberFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowRightSection_right,
    twistedIdentityFiberInclusion, pullback.lift_snd]

/-- 同じ全族を、元の同じ fiber の twisted arrow 内で読む。 -/
def twistedIdentityFiberLift : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseVertexFiberLift p b (twistedIdentityFiberFamily p b) (twistedIdentityFiberFamily_base p b)

/-- 元の全空間へ戻すと、同じ大域切断を制限した全族そのもの。 -/
lemma twistedIdentityFiberLift_map :
    twistedIdentityFiberLift p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) =
      twistedIdentityFiberFamily p b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseVertexFiberLift_map p b _ _

/-- 同じ fiber の中の右端は、全次数で恒等写像。 -/
lemma twistedIdentityFiberLift_right :
    twistedIdentityFiberLift p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality, ← Category.assoc,
    twistedIdentityFiberLift_map, twistedIdentityFiberFamily_right, Category.id_comp]

/-- 同じ大域評価の恒等点上の作用を、元の反転した fiber 内で読む。 -/
def twistedIdentityFiberEvaluation : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).op :=
  twistedIdentityFiberLift p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)

/-- 同じ恒等点評価は、元の大域的な左端評価の制限そのもの。 -/
lemma twistedIdentityFiberEvaluation_ι :
    twistedIdentityFiberEvaluation p b ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) =
      twistedIdentityFiberInclusion p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowSourceLift p := by
  rw [twistedIdentityFiberEvaluation, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality,
    ← Category.assoc, twistedIdentityFiberLift_map]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
