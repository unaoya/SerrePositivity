module

public import SerrePositivity.InfinityCategories.Sheaves.LocalEquivalenceImageReduction
public import SerrePositivity.InfinityCategories.Sheaves.MonoLocalSections

/-!
概要：元の全有限次数の Čech 対角と像の包含に、既証の単射の場合の切断比較を適用する。
方針：同じ対角の分裂単射性と局所全射性を、同じ指定 sectionsOf_map に入れる。
規約：HTT 6.2.2.6 の局所性への入力。係数 E に presentable 性を追加しない。
使われ方：S8 の一般の局所同値の二つの段階。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 同じ像の包含に沿う指定全錐の制限は、元の層の係数で極限錐。 -/
lemma rangeInclusion_restrictSectionsCone_isLimit (J : GrothendieckTopology C) (f : P ⟶ Q)
    [CategoryTheory.Presheaf.IsLocallySurjective J f]
    (O : Presheaf C E) (hO : IsSheaf J O)
    (c : JoinCone (sectionsOfDiagram Q O)) (hc : IsLimitCone c) :
    IsLimitCone (SetWeight.restrictSectionsCone (Subfunctor.range f).ι O c) := by
  letI := rangeInclusion_isLocallySurjective J f
  exact restrictSectionsCone_isLimit_of_localMono J (Subfunctor.range f).ι O hO c hc

/-- 同じ元の Čech 対角の指定切断比較は、零次を含む全次数で可逆。 -/
lemma relativeCechDiagonal_sections_isInvertible (J : GrothendieckTopology C) (f : P ⟶ Q)
    [CategoryTheory.Presheaf.IsLocallyInjective J f]
    (j : AsSmall.{u} SimplexCategoryᵒᵖ) (O : Presheaf C E) (hO : IsSheaf J O)
    (hP : HasLimit (sectionsOfDiagram P O))
    (hD : HasLimit (sectionsOfDiagram ((relativeCechDiagram f).obj j) O)) :
    IsInvertibleEdge
      (sectionsOf_map ((relativeCechDiagonal f).app j) O hP hD).toTruncated :=
  sections_localMono_iso J ((relativeCechDiagonal f).app j) O hO hP hD

end SerrePositivity.InfinityCategories.Sheaves
