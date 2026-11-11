module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift

/-!
概要：同じ実中央辺を元 gluing の固定 ν 値から増大屋根として回収する。
方針：既存の同じ増大の ν 同値の逆と中央辺を合成する。
規約：この屋根比較は native lax 中央射との全比較とは区別する。
使われ方：d④ の増大境界を固定する全関手同型。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元 gluing の固定 ν 値から同じ実中央辺への増大屋根。
方針：保存済み増大同値の逆を実中央辺へ合成する。
規約：厳密 dg 逆増大を仮定しない。使われ方：中央辺の元始域回収。 -/
def dgOdotMilnorRightAxisNuRoof : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotGluingInput R d))
    (dgKInputStableValue R (dgOdotMilnorRightAxisInput R d)) where
  hom := (dgOdotMilnorAugmentationNuEquivalence R d).inv ≫
    (dgOdotMilnorRightAxisExactMap R d).hom
  isExact := by
    letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgOdotMilnorAugmentationNuEquivalence R d).inv :=
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
        (dgOdotMilnorAugmentationNuEquivalence R d).symm.isQCatEquivalence
    letI := (dgOdotMilnorRightAxisExactMap R d).isExact
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _

/-- 概要：同じ増大上で屋根は元中央辺の全 ν 関手を回収する。
方針：元増大同値の指定単位を同じ実中央辺で後合成する。
規約：全単体を保持し、導来 bimodule の射等号で代用しない。
使われ方：中央辺を貼る際の指定増大境界。 -/
def dgOdotMilnorRightAxisNuRoof_comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorAugmentationExactMap R d).hom ≫
      (dgOdotMilnorRightAxisNuRoof R d).hom)
    (dgOdotMilnorRightAxisExactMap R d).hom := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorAugmentationNuEquivalence R d).hom ≫
      ((dgOdotMilnorAugmentationNuEquivalence R d).inv ≫
        (dgOdotMilnorRightAxisExactMap R d).hom)) _
  rw [← Category.assoc]
  simpa only [Category.id_comp] using
    ((dgOdotMilnorAugmentationNuEquivalence R d).homInvIso.postcomp
      (dgOdotMilnorRightAxisExactMap R d).hom)

end SerrePositivity.KST.SConstruction
