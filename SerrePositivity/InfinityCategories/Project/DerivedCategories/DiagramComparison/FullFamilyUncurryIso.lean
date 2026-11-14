module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoPair

/-!
概要：関手圏の全族同型を、元の二変数の共同評価の全族同型へ戻す。
方針：既存の組の関手同型に評価を後合成し、curryの余単位の式を使う。
規約：点ごとの同型を新たな自然性の仮定として使わない。
使われ方：3b-3 R6 U32、同じ全余錐族のuncurry。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- U32の前提計算：既存の評価の余単位は全関手同型を共同評価へ運ぶ。 -/
def fullFamilyUncurryIso {P K D : SSet.{u}} [Quasicategory D]
    {F G : K ⟶ (ihom P).obj D} (e : FunctorIso F G) :
    FunctorIso (uncurry F) (uncurry G) := by
  have h := (SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIsoLiftRight
    (e.precomp (snd P K)) (fst P K)).postcomp
      ((β_ ((ihom P).obj D) P).hom ≫ (ihom.ev P).app D)
  have hp (f : K ⟶ (ihom P).obj D) :
      lift (snd P K ≫ f) (fst P K) ≫ (β_ ((ihom P).obj D) P).hom = P ◁ f := by
    rw [lift_braiding_hom, ← lift_whiskerLeft, lift_fst_snd, Category.id_comp]
  rw [← Category.assoc, hp, ← Category.assoc, hp] at h
  simpa only [uncurry_eq] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
