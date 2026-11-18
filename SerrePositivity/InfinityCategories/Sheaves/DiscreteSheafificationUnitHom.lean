module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.OrdinarySheafificationUnitHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence

/-!
概要：集合値層化の単位を離散前層の全関手間の射として読む。
方針：指定された同じ円柱をカリー化し、その辺の類を取る。
  文献対応：HTT 6.2.2.7・5.5.4.15 の離散係数の場合。
使われ方：指定層化単位の反転と層化の比較。
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 元の集合値層化単位の全円柱が定める、離散前層間の指定射。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site の離散係数の層化単位。"]
def discreteSheafificationUnitHom :
    ∀ {C : Type u} [SmallCategory C]
      (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
    let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
    let I := (discretePresheafInclusion C).val
    FunctorHom I (nerveMap S ≫ I) :=
  fun J hJ => Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (ordinarySheafificationUnit_postHomotopy J hJ))

end SerrePositivity.InfinityCategories.Sheaves
