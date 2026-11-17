module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationFunctorIsoLift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：指定された底の関手同型を、引き戻し間の射とその第一射影の同型へ移す。
方針：既存の関手同型の持ち上げを第一射影に適用し、終点を引き戻しの普遍性で戻す。
規約：HTT 2.1.1.6、Kerodon Tag 019Kの既存構成の法則。
  指定された底の同型の類をHEqで保持する。単なる同型の存在へ弱めない。
使われ方：R04の元の添字同型とその逆の持ち上げによる局所形状の比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

private lemma isoTransport_postcomp_heq {A X Y : SSet.{u}}
    {f g f' g' : A ⟶ X} (i : FunctorIso f g) (hf : f = f') (hg : g = g')
    (p : X ⟶ Y) : HEq ((functorIsoOfEq i hf hg).postcomp p) (i.postcomp p) := by
  subst f' g'
  rfl

/-- 引き戻し間の射の第一射影の比較は、同じ底の指定同型の前合成を回収する。 -/
@[cite HTT "2.1.1.6" (partial := special) "指定同型の持ち上げを引き戻しの普遍性へ移す法則。"]
lemma exists_leftPullbackFunctorIsoLift {E B K : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    {f g : K ⟶ B} (e : FunctorIso f g) :
    ∃ (a : pullback p f ⟶ pullback p g)
      (ha : a ≫ pullback.snd p g = pullback.snd p f)
      (L : FunctorIso (pullback.fst p f) (a ≫ pullback.fst p g)),
      HEq (L.postcomp p) (e.precomp (pullback.snd p f)) := by
  let π := pullback.snd p f
  let e₀ : FunctorIso (pullback.fst p f ≫ p) (π ≫ g) :=
    functorIsoOfEq (e.precomp π) pullback.condition.symm rfl
  obtain ⟨l, hl, i, hi⟩ := exists_leftFibration_functorIso_lift p (pullback.fst p f) e₀
  let a := pullback.lift l π hl
  let L : FunctorIso (pullback.fst p f) (a ≫ pullback.fst p g) :=
    functorIsoOfEq i rfl (pullback.lift_fst l π hl).symm
  refine ⟨a, pullback.lift_snd _ _ _, L, ?_⟩
  have h₁ : HEq (L.postcomp p) (i.postcomp p) := isoTransport_postcomp_heq _ _ _ _
  have h₂ : HEq (i.postcomp p) e₀ :=
    (functorIsoOfEq_heq (i.postcomp p) rfl hl).symm.trans (heq_of_eq hi)
  exact h₁.trans (h₂.trans (functorIsoOfEq_heq (e.precomp π) pullback.condition.symm rfl))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
