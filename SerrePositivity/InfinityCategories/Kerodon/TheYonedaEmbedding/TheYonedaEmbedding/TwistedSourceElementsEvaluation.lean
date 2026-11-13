module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TwistedSourceElementsComparison
public import SerrePositivity.InfinityCategories.HTT.Section2_1_3.VertexFiberOpposite

/-!
概要：同じ始点を持つ全族の大域評価を、元の反転した fiber 内で読む。
方針：同じ元の大域切断の左端を固定 fiber へ持ち上げ、反転 fiber の標準同型で戻す。
規約：恒等点での作用は構成済みの同じ評価と厳密に一致する。
使われ方：元の密度余錐の各評価の弱同値性を示す全空間側の比較。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (b : B _⦋0⦌)

/-- 始点固定の全族に制限した、同じ大域左端評価。 -/
def twistedSourceElementsSourceMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElements p b ⟶ E.op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowSourceLift p

/-- 同じ左端評価は、全次数で指定した反転した始点を被覆する。 -/
lemma twistedSourceElementsSourceMap_projection :
    twistedSourceElementsSourceMap p b ≫ SSet.opFunctor.map p =
      SSet.const (SSet.opObjEquiv.symm b) := by
  have hl : pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection B) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion b) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft B = SSet.const (SSet.opObjEquiv.symm b) := by
    have h := congrArg (fun f ↦ f ≫ fst B.op B)
      (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection B) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion b))
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion,
      lift_fst, SSet.comp_const] using h
  rw [twistedSourceElementsSourceMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowSourceLift_projection,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison_fst, Category.assoc, hl, SSet.comp_const]

/-- 同じ全族の評価を、元の反転した fiber 内の一つの射として固定する。 -/
def twistedSourceElementsEvaluation : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElements p b ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b)
    (twistedSourceElementsSourceMap p b) (twistedSourceElementsSourceMap_projection p b) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso p b).inv

/-- 元の全空間へ含めると、構成済みの同じ大域評価の制限そのもの。 -/
lemma twistedSourceElementsEvaluation_ι :
    twistedSourceElementsEvaluation p b ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) =
      twistedSourceElementsSourceMap p b := by
  have hi : (_root_.SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso p b).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) := by rfl
  rw [twistedSourceElementsEvaluation, Category.assoc, hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

/-- 始対象の fiber に制限すると、元の大域切断から取った同じ恒等点評価を回収する。 -/
lemma twistedSourceElementsEvaluation_identity [Quasicategory B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsIdentityInclusion p b ≫ twistedSourceElementsEvaluation p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedIdentityFiberEvaluation p b := by
  have : Mono (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    intro x y h
    exact Subtype.ext h
  apply (cancel_mono (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))).mp
  rw [Category.assoc, twistedSourceElementsEvaluation_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedIdentityFiberEvaluation_ι,
    twistedSourceElementsSourceMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison_identity]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
