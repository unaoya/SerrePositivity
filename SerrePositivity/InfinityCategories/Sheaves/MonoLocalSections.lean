module

public import SerrePositivity.InfinityCategories.Sheaves.MonoLocalRightKanRestriction
public import SerrePositivity.InfinityCategories.Sheaves.SieveSectionsCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeReindexRestrictions

/-!
概要：局所全射な単射に対し、元の sectionsOf_map が可逆であることを証明する。
方針：同じ指定極限錐を AsSmall に移し、右 Kan による制限の極限性を元の全錐へ戻す。
規約：HTT 6.2.2.6 の層条件から導く S8 の単射の場合。任意の頂点同型で射を置き換えない。
使われ方：一般の局所同値の切断の不変性への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の係数図式とその AsSmall 表示は、同じ添字の同型で対応する。 -/
lemma asSmallSectionsDiagram_eq (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E) :
    asSmallSectionsDiagram P O =
      (nerveAsSmallIso P.Elements).inv ≫ sectionsOfDiagram P O := rfl

/-- 元の全錐を、係数を保って同じ AsSmall の表示へ移す。 -/
def asSmallSectionsCone (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
    (c : JoinCone (sectionsOfDiagram P O)) : JoinCone (asSmallSectionsDiagram P O) :=
  (c.reindexIso (nerveAsSmallIso P.Elements).symm).cast (asSmallSectionsDiagram_eq P O).symm

/-- 同じ元の錐の AsSmall 表示は極限性を保つ。 -/
lemma asSmallSectionsCone_isLimit (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
    (c : JoinCone (sectionsOfDiagram P O)) (hc : IsLimitCone c) :
    IsLimitCone (asSmallSectionsCone P O c) :=
  ((isLimitCone_iff_reindexIso c (nerveAsSmallIso P.Elements).symm).mp hc).cast _

/-- AsSmall で制限した全錐を元の添字に戻すと、同じ指定切断の制限錐になる。 -/
lemma asSmallSectionsCone_restrict_val (φ : P ⟶ Q) (O : Presheaf C E)
    (c : JoinCone (sectionsOfDiagram Q O)) :
    ((restrictJoinCone (asSmallSectionsCone Q O c)
      (nerveMap (asSmallLocalFunctor φ.mapElements))).reindexIso
        (nerveAsSmallIso P.Elements)).val = (SetWeight.restrictSectionsCone φ O c).val := by
  change joinMap (𝟙 _) (nerveAsSmallIso P.Elements).hom ≫
    (joinMap (𝟙 _) (nerveMap (asSmallLocalFunctor φ.mapElements)) ≫
      (joinMap (𝟙 _) (nerveAsSmallIso Q.Elements).inv ≫ c.val)) =
    joinMap (𝟙 _) (SetWeight.elementsMap φ) ≫ c.val
  simp only [← Category.assoc, ← joinMap_comp, Category.id_comp]
  rfl

/-- 局所全射な単射に沿う元の指定全錐の制限は、層の係数で極限錐になる。 -/
lemma restrictSectionsCone_isLimit_of_localMono (J : GrothendieckTopology C)
    (φ : P ⟶ Q) [Mono φ] [CategoryTheory.Presheaf.IsLocallySurjective J φ]
    (O : Presheaf C E) (hO : IsSheaf J O)
    (c : JoinCone (sectionsOfDiagram Q O)) (hc : IsLimitCone c) :
    IsLimitCone (SetWeight.restrictSectionsCone φ O c) := by
  have hl := monoLocal_restrict_isLimit J φ O hO (asSmallSectionsCone Q O c)
    (asSmallSectionsCone_isLimit Q O c hc)
  have hr := (isLimitCone_iff_reindexIso _ (nerveAsSmallIso P.Elements)).mp hl
  exact (isLimitCone_iff_of_cone_val_eq _ _ (asSmallSectionsCone_restrict_val φ O c)).mp hr

/-- 局所全射な単射に沿う、元の指定 sectionsOf_map は可逆。
同じ指定錐の比較辺を使い、存在だけの頂点同型に置き換えない。 -/
lemma sections_localMono_iso (J : GrothendieckTopology C)
    (φ : P ⟶ Q) [Mono φ] [CategoryTheory.Presheaf.IsLocallySurjective J φ]
    (O : Presheaf C E) (hO : IsSheaf J O)
    (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)) :
    IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated :=
  (sectionsMap_isInvertible_iff φ O (sectionsOfCone P O hP) (sectionsOfCone_isLimit P O hP)
    (sectionsOfCone Q O hQ) (sectionsOfCone_isLimit Q O hQ)).mpr
      (restrictSectionsCone_isLimit_of_localMono J φ O hO
        (sectionsOfCone Q O hQ) (sectionsOfCone_isLimit Q O hQ))

end SerrePositivity.InfinityCategories.Sheaves
