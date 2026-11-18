module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.SheafifyDiscreteFunctorIso

/-!
概要：離散層化の全比較は、同じ通常層化の指定単位と可換。
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

/-- 離散層化の全比較は、同じ通常層化の指定単位と可換。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散係数の指定層化単位。"]
lemma sheafifyDiscreteFunctorIso_unit_fac :
∀ {C : Type u} [SmallCategory C]
 (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
let I := (discretePresheafInclusion C).val
functorHomPrecomp (𝟙 (PresheafCat C SpaceInfinity.{u}))
 (sheafificationFunctor J hJ) I (Classical.choice hJ).unit ≫
 (sheafifyDiscreteFunctorIso J hJ).hom = discreteSheafificationUnitHom J hJ := by
  intro C hC J hJ S I
  exact (specifiedDiscreteSheafificationMate J hJ).property

end SerrePositivity.InfinityCategories.Sheaves
