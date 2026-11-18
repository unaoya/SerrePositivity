module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.SectionsSpaceToRangeIso
public import SerrePositivity.InfinityCategories.Sheaves.SectionsOfMapComposition
public import SerrePositivity.InfinityCategories.Sheaves.RelativeCechLocalSections

/-!
概要：集合値の局所同値に沿う空間値の指定切断の写像は可逆。
方針：元の指定切断の辺をホモトピー圏で比較する。
  文献対応：HTT 6.2.2.6（集合値前層の局所同値の場合）。
使われ方：一般の層の係数に対する切断の局所性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 集合値の局所同値に沿う空間値の指定切断の写像は可逆。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の集合値前層と空間値の切断。"]
lemma sections_localEquiv_iso_space :
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C SpaceInfinity.{u}) (hO : IsSheaf J O)
  (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)),
  IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated := by
  intro C hC J P Q φ hφ O hO hP hQ
  obtain ⟨hinj, hsurj⟩ := (isLocalEquivSet_iff_locallyBijective J φ).mp hφ
  letI : CategoryTheory.Presheaf.IsLocallyInjective J φ := hinj
  letI : CategoryTheory.Presheaf.IsLocallySurjective J φ := hsurj
  let R := (Subfunctor.range φ).toFunctor
  let hR := sectionsOfDiagram_hasLimit space_isPresentable.{u} R O
  let g : P ⟶ R := Subfunctor.toRange φ
  let i : R ⟶ Q := (Subfunctor.range φ).ι
  letI : CategoryTheory.Presheaf.IsLocallySurjective J i := rangeInclusion_isLocallySurjective J φ
  letI : IsIso (homMk (sectionsOf_map g O hP hR).toTruncated) :=
    sections_toRange_isInvertible_space J φ O hO hP hR
  letI : IsIso (homMk (sectionsOf_map i O hR hQ).toTruncated) :=
    sections_localMono_iso J i O hO hR hQ
  have hgi : g ≫ i = φ := Subfunctor.toRange_ι φ
  change IsIso (homMk (sectionsOf_map φ O hP hQ).toTruncated)
  rw [← hgi, sectionsOf_map_comp_hom g i O hP hR hQ]
  infer_instance

end SerrePositivity.InfinityCategories.Sheaves
