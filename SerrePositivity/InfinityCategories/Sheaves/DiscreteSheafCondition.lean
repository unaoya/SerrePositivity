module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteNerveConeReflection
public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafPointwise
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscreteSpaceLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConePostcompose
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FullyFaithfulConeReflection
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
概要：離散空間値の元の層条件と、同じ集合値前層の通常の層条件は同値。
方針：同じ指定篩錐の全射を比較し、極限の保存と充満忠実な離散埋め込みによる反映を使う。
規約：HTT 6.2.2.6・6.2.2.7 の小さい通常 site と離散係数の場合。
Kerodon §7.1（Tag 02H1）の指定極限錐への特殊化で、一般の係数の層化比較ではない。
使われ方：S8 の離散層化を元の集合値層化の単位へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 元の指定篩錐は Mathlib の同じ篩の通常の錐に一致する。 -/
lemma sieveCone_eq_presieveCone {U : C} (S : Sieve U) :
    sieveCone S = S.arrows.cocone.op := rfl

/-- 元の制限全錐は、同じ通常錐を離散係数で送った coherent 錐。 -/
lemma restrictionCone_discrete_val (P : Cᵒᵖ ⥤ Type u) {U : C} (S : Sieve U) :
    (restrictionCone (discretePresheaf P) S).val =
      (discreteSpaceCone (P.mapCone (sieveCone S))).val :=
  (strictCoherentConeMap_mapCone (sieveCone S) (P ⋙ setsToKan)).symm

/-- 離散空間値層の元の指定錐の条件は、同じ集合値前層の通常の層条件。
HTT 6.2.2.6・6.2.2.7 の小さい通常 site と離散係数の場合。 -/
@[cite HTT "6.2.2.7" (partial := special)
  "小さい通常 site の集合値前層と、その同じ離散空間値前層の層条件の一致。"]
lemma isSheaf_discretePresheaf_iff (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type u) :
    IsSheaf J (discretePresheaf P) ↔ CategoryTheory.Presheaf.IsSheaf J P := by
  constructor
  · intro h
    rw [CategoryTheory.Presheaf.isSheaf_iff_isLimit]
    intro U S hS
    have hl := h U S hS
    rw [← smallNerveDiagram_discrete] at hl
    let c := ((nerveCone (sieveCone S)).ulift).postcomp (smallNerveDiagram P)
    have hv : (mapJoinCone discreteSpaceInclusion c).val =
        (restrictionCone (smallNerveDiagram P ≫ discreteSpaceInclusion) S).val := by
      simp only [mapJoinCone, c, restrictionCone, JoinCone.postcomp, Category.assoc]
    have hi := (isLimitCone_iff_of_cone_val_eq _ _ hv).mpr hl
    have hr := isLimitCone_of_fullyFaithful_image discreteSpaceInclusion
      discreteSpaceInclusion_isFullyFaithful c hi
    simpa only [sieveCone_eq_presieveCone] using
      smallNerveDiagram_reflects_limit (sieveCone S) P hr
  · intro h U S hS
    obtain ⟨hc⟩ := ((CategoryTheory.Presheaf.isSheaf_iff_isLimit (J := J) (P := P)).mp h) S hS
    have hc' : IsLimit (P.mapCone (sieveCone S)) := hc
    exact (isLimitCone_iff_of_cone_val_eq _ _ (restrictionCone_discrete_val P S)).mpr
      (discreteSpaceCone_isLimit _ hc')

end SerrePositivity.InfinityCategories.Sheaves
