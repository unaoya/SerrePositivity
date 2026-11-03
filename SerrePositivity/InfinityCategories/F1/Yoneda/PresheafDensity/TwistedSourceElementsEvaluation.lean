module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedSourceElementsComparison
public import SerrePositivity.InfinityCategories.Core.VertexFiberOpposite

/-!
概要：同じ始点を持つ全族の大域評価を、元の反転した fiber 内で読む。
方針：同じ元の大域切断の左端を固定 fiber へ持ち上げ、反転 fiber の標準同型で戻す。
規約：恒等点での作用は構成済みの同じ評価と厳密に一致する。
使われ方：元の密度余錐の各評価の弱同値性を示す全空間側の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E B : SSet.{u}} (p : E ⟶ B) [RightFibration p] (b : B _⦋0⦌)

/-- 始点固定の全族に制限した、同じ大域左端評価。 -/
def twistedSourceElementsSourceMap : twistedSourceElements p b ⟶ E.op :=
  twistedSourceElementsComparison p b ≫ twistedArrowSourceLift p

/-- 同じ左端評価は、全次数で指定した反転した始点を被覆する。 -/
lemma twistedSourceElementsSourceMap_projection :
    twistedSourceElementsSourceMap p b ≫ SSet.opFunctor.map p =
      SSet.const (SSet.opObjEquiv.symm b) := by
  have hl : pullback.fst (twistedArrowProjection B) (twistedArrowSourceInclusion b) ≫
      edgewiseLeft B = SSet.const (SSet.opObjEquiv.symm b) := by
    have h := congrArg (fun f ↦ f ≫ fst B.op B)
      (pullback.condition (f := twistedArrowProjection B) (g := twistedArrowSourceInclusion b))
    simpa only [Category.assoc, twistedArrowProjection_fst, twistedArrowSourceInclusion,
      lift_fst, SSet.comp_const] using h
  rw [twistedSourceElementsSourceMap, Category.assoc, twistedArrowSourceLift_projection,
    ← Category.assoc, twistedSourceElementsComparison_fst, Category.assoc, hl, SSet.comp_const]

/-- 同じ全族の評価を、元の反転した fiber 内の一つの射として固定する。 -/
def twistedSourceElementsEvaluation : twistedSourceElements p b ⟶ (vertexFiber p b).op :=
  vertexFiberLift (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b)
    (twistedSourceElementsSourceMap p b) (twistedSourceElementsSourceMap_projection p b) ≫
      (vertexFiberOpIso p b).inv

/-- 元の全空間へ含めると、構成済みの同じ大域評価の制限そのもの。 -/
lemma twistedSourceElementsEvaluation_ι :
    twistedSourceElementsEvaluation p b ≫ SSet.opFunctor.map (vertexFiberι p b) =
      twistedSourceElementsSourceMap p b := by
  have hi : (vertexFiberOpIso p b).inv ≫ SSet.opFunctor.map (vertexFiberι p b) =
      vertexFiberι (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) := by rfl
  rw [twistedSourceElementsEvaluation, Category.assoc, hi, vertexFiberLift_ι]

/-- 始対象の fiber に制限すると、元の大域切断から取った同じ恒等点評価を回収する。 -/
lemma twistedSourceElementsEvaluation_identity [Quasicategory B] :
    twistedSourceElementsIdentityInclusion p b ≫ twistedSourceElementsEvaluation p b =
      twistedIdentityFiberEvaluation p b := by
  have : Mono (SSet.opFunctor.map (vertexFiberι p b)) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    intro x y h
    exact Subtype.ext h
  apply (cancel_mono (SSet.opFunctor.map (vertexFiberι p b))).mp
  rw [Category.assoc, twistedSourceElementsEvaluation_ι, twistedIdentityFiberEvaluation_ι,
    twistedSourceElementsSourceMap, ← Category.assoc, twistedSourceElementsComparison_identity]

end SerrePositivity.InfinityCategories.F2.Ind
