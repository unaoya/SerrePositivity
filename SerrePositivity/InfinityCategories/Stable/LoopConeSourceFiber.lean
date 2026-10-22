module
public import SerrePositivity.InfinityCategories.Stable.LoopConeClassifier
public import SerrePositivity.InfinityCategories.Stable.PointedConeLeftFibration
/-!
概要：全 loop cospan 上の錐の始点固定 fiber は、固定頂点からの錐射影の引き戻し。
方針：任意パラメータの持ち上げと一意性を厳密 fiber で確認し、left fibration 性を移す。
規約：X の quasicategory 性だけを使う。使われ方：実 comma 比較の fiber ごとの同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 始点固定の全 loop 錐を、同じ固定頂点からの全錐へ送る。 -/
def loopConeSourceFiberDiagram (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌) :
    vertexFiber (loopConeObjectSource X) x ⟶ pointedConeFamily (horn 2 2 : SSet.{u}) X x :=
  vertexFiberMap (loopConeObjectSource X) (coneApexEvaluation (horn 2 2 : SSet.{u}) X)
    (loopConeObjectDiagram X) rfl x

/-- 始点固定の全 loop 錐から loop 図式への実射影。 -/
def loopConeSourceFiberProjection (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌) :
    vertexFiber (loopConeObjectSource X) x ⟶ loopDiagrams X :=
  vertexFiberι (loopConeObjectSource X) x ≫ loopConeObjectLoop X

/-- 始点固定の全 loop 錐は、固定頂点からの錐射影の厳密な引き戻し。 -/
lemma loopConeSourceFiber_isPullback (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌) :
    IsPullback (loopConeSourceFiberDiagram X x) (loopConeSourceFiberProjection X x)
      (pointedConeProjection (horn 2 2 : SSet.{u}) X x)
      (loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X) := by
  let p := coneRestriction (horn 2 2 : SSet.{u}) X
  let P := loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X
  let a := coneApexEvaluation (horn 2 2 : SSet.{u}) X
  have hdiag : loopConeSourceFiberDiagram X x ≫ vertexFiberι a x =
      vertexFiberι (loopConeObjectSource X) x ≫ loopConeObjectDiagram X :=
    vertexFiberMap_ι _ _ _ _ _
  have hw : loopConeSourceFiberDiagram X x ≫ pointedConeProjection (horn 2 2 : SSet.{u}) X x =
      loopConeSourceFiberProjection X x ≫ P := by
    change loopConeSourceFiberDiagram X x ≫ vertexFiberι a x ≫ p = _
    rw [← Category.assoc, hdiag]
    change vertexFiberι (loopConeObjectSource X) x ≫ pullback.fst p P ≫ p =
      (vertexFiberι (loopConeObjectSource X) x ≫ pullback.snd p P) ≫ P
    rw [Category.assoc, pullback.condition]
  apply IsPullback.mk' hw
  · intro T f g hf hg
    apply vertexFiber_hom_ext (loopConeObjectSource X) x
    apply pullback.hom_ext
    · have hh := congrArg (fun q ↦ q ≫ vertexFiberι a x) hf
      simpa only [Category.assoc, hdiag] using hh
    · exact hg
  · intro T b c hbc
    have hb : (b ≫ vertexFiberι a x) ≫ p = c ≫ P := hbc
    let d := pullback.lift (b ≫ vertexFiberι a x) c hb
    have hd : d ≫ loopConeObjectSource X = SSet.const x := by
      change (pullback.lift (b ≫ vertexFiberι a x) c hb ≫ pullback.fst p P) ≫ a = _
      rw [pullback.lift_fst, Category.assoc, vertexFiberι_comp, SSet.comp_const]
    let l := vertexFiberLift (loopConeObjectSource X) x d hd
    refine ⟨l, ?_, ?_⟩
    · apply vertexFiber_hom_ext a x
      rw [Category.assoc, hdiag, ← Category.assoc, vertexFiberLift_ι]
      exact pullback.lift_fst _ _ _
    · change l ≫ vertexFiberι (loopConeObjectSource X) x ≫ pullback.snd p P = c
      rw [← Category.assoc, vertexFiberLift_ι]
      exact pullback.lift_snd _ _ _

/-- 始点固定の全 loop 錐の射影は左ファイブレーション。 -/
instance loopConeSourceFiberProjection_leftFibration (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) : LeftFibration (loopConeSourceFiberProjection X x) :=
  ⟨leftFibrations.of_isPullback (loopConeSourceFiber_isPullback X x)
    (LeftFibration.mem (p := pointedConeProjection (horn 2 2 : SSet.{u}) X x))⟩
/-- 始点固定の全 loop 錐は quasicategory。 -/
instance loopConeSourceFiber_quasicategory (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) : Quasicategory (vertexFiber (loopConeObjectSource X) x) :=
  quasicategory_of_innerFibration (loopConeSourceFiberProjection X x)
end SerrePositivity.InfinityCategories
