module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteSheafificationMateIso

/-!
概要：通常層化と前層準圏の層化を、離散前層の全図式で比較する。
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

/-- 全単位の式を保持するように選んだ指定 mate。 -/
def specifiedDiscreteSheafificationMate {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}) :
    let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
    let I := (discretePresheafInclusion C).val
    { m : FunctorHom (I ≫ sheafificationFunctor J hJ) (nerveMap S ≫ I) //
      functorHomPrecomp (𝟙 (PresheafCat C SpaceInfinity.{u}))
        (sheafificationFunctor J hJ) I (Classical.choice hJ).unit ≫ m =
          discreteSheafificationUnitHom J hJ } := by
  let h := discreteSheafification_mate_exists_specified J hJ (discreteSheafificationUnitHom J hJ)
    (discreteSheafificationUnitHom_evaluate J hJ) (discreteSheafificationUnitHom_post_isIso J hJ)
  exact ⟨h.choose, h.choose_spec⟩

/-- 通常層化と前層準圏の層化を、離散前層の全図式で比較する。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散係数の指定層化単位。"]
def sheafifyDiscreteFunctorIso :
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
  FunctorIso
    ((discretePresheafInclusion C).val ≫ sheafificationFunctor J hJ)
    (nerveMap (presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)) ≫
      (discretePresheafInclusion C).val) := by
  intro C hC J hJ
  let p := specifiedDiscreteSheafificationMate J hJ
  letI : IsIso p.val := discreteSheafification_specifiedMate_isIso J hJ _
    (discreteSheafificationUnitHom_post_isIso J hJ) p.val p.property
  exact asIso p.val

end SerrePositivity.InfinityCategories.Sheaves
