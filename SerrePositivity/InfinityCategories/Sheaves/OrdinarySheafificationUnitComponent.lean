module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.OrdinarySheafificationUnitHomotopy

/-!
概要：通常の層化の指定単位が定める空間値前層の円柱。
方針：集合値の全自然変換の nerve 円柱を、指定された離散前層の埋め込みで後合成する。
  文献対応：HTT 6.2.2.7・5.5.4.15 の離散係数の場合。
使われ方：層化の比較射とその各成分を同じ円柱から読む。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 指定した全円柱の成分は、元の層化単位の成分を埋め込んだ辺である。 -/
@[cite HTT "6.2.2.7" (partial := special) "離散係数の層化単位の成分を読む。"]
lemma ordinarySheafificationUnit_postHomotopy_component :
    ∀ {C : Type u} [SmallCategory C]
      (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
    let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
    let I := (discretePresheafInclusion C).val
    ∀ P : Cᵒᵖ ⥤ Type u,
      (simplicialHomotopyVertexEdge (ordinarySheafificationUnit_postHomotopy J hJ)
        (nerveVertex P)).edge =
      ((nerve.edgeMk (CategoryTheory.toSheafify J P)).map I).edge := by
  intro C hC J hJ S I P
  let η := (sheafificationAdjunction J (Type u)).unit
  change I.app _ (simplicialHomotopyVertexEdge
    (largeNerveNatTransHomotopy η) (nerveVertex P)).edge = _
  rw [largeNerveNatTransHomotopy_component]
  rfl

end SerrePositivity.InfinityCategories.Sheaves
