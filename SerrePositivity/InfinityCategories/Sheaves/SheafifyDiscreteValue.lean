module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.SheafifyDiscreteFunctorUnit

/-!
概要：離散前層の指定層化は、通常の集合値層化を離散とした前層と同型。
方針：同じ通常層化の単位の全円柱とその頂点成分を使う。
  文献対応：HTT 6.2.2.7・5.5.4.15。
使われ方：離散係数の指定層化の全比較。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 離散前層の指定層化は、通常の集合値層化を離散とした前層と同型。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散係数の指定層化単位。"]
def sheafify_discrete_eq :
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
  (P : Cᵒᵖ ⥤ Type u),
  FunctorIso (sheafify J hJ (discretePresheaf P))
    (discretePresheaf (((presheafToSheaf J (Type u)).obj P).obj)) := by
  intro C hC J hJ P
  let X := PresheafCat C SpaceInfinity.{u}
  let L := sheafificationFunctor J hJ
  let I := (discretePresheafInclusion C).val
  let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
  let v := nerveVertex P
  let e := sheafifyDiscreteFunctorIso J hJ
  let h₁ := (discretePresheafInclusion C).property.1 P
  have h₂ : (nerveMap S ≫ I).app _ v = functorVertex (discretePresheaf (S.obj P)) :=
    (congrArg (fun w => I.app _ w) (nerveMap_app_mk₀ S P)).trans
      ((discretePresheafInclusion C).property.1 (S.obj P))
  let h₃ := functorVertex_sheafify J hJ (discretePresheaf P)
  let q : X _⦋0⦌ → X _⦋0⦌ := L.app (Opposite.op ⦋0⦌)
  let c₃ := eqToIso (congrArg HomotopyCategory.mk h₃)
  let c₁ := eqToIso (congrArg HomotopyCategory.mk (congrArg q h₁.symm))
  let c₂ := eqToIso (congrArg HomotopyCategory.mk h₂)
  let m := functorHomEvaluate e.hom v
  letI : IsIso m := inferInstanceAs (IsIso (functorHomEvaluate e.hom v))
  exact c₃ ≪≫ c₁ ≪≫ asIso m ≪≫ c₂

end SerrePositivity.InfinityCategories.Sheaves
