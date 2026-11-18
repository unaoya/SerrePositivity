module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.SectionsSpaceLocalEquivalence
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteSectionsLocality

/-!
概要：集合値局所同値の離散表示に対して、空間値の層は局所対象。
方針：同じ要素圏切断の可逆性を局所 Hom の判定に入れる。
  文献対応：HTT 5.5.4.20、通常の小さい site の集合値前層の場合。
使われ方：離散前層の層化の指定比較。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 集合値局所同値の離散表示に対して、空間値の層は局所対象。 -/
@[cite HTT "5.5.4.20" (partial := special) "小さい通常の site の離散前層の層化の比較。"]
lemma discreteHom_isLocalForHom_of_localEquiv :
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C SpaceInfinity.{u}) (hO : IsSheaf J O),
  IsLocalForHom (discretePresheafHom φ) (functorVertex O) := by
  intro C hC J P Q φ hφ O hO
  let hP := sectionsOfDiagram_hasLimit space_isPresentable.{u} P O
  let hQ := sectionsOfDiagram_hasLimit space_isPresentable.{u} Q O
  exact (discreteHom_precomposition_sections_detects_locality φ O hP hQ).mpr
    (sections_localEquiv_iso_space J φ hφ O hO hP hQ)

end SerrePositivity.InfinityCategories.Sheaves
