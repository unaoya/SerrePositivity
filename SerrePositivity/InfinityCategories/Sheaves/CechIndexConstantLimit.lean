module

public import SerrePositivity.InfinityCategories.Sheaves.CechPointElements
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.WeaklyContractibleConstantLimit
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.WeakContractibleContractionSpan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallBousfieldKanWeight
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：元の反転 Čech 添字上の定値錐を、指定頂点を保った極限錐として使う。
方針：単体圏の零次の終性を反対圏で使い、既存の定値錐の弱可縮添字による判定へ渡す。
規約：HTT 4.1.3.1、Kerodon §7.2（Tag 02MZ）の既存の収縮と形状移送の法則。
使われ方：S8 の同じ Čech 対角を定値な切断の錐と比較する。係数の presentable 性は不要。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 元の Čech 添字の反転を、係数と同じ単体集合の宇宙で保持する。 -/
abbrev cechReverseIndex : SSet.{u + 1} :=
  ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} SimplexCategoryᵒᵖ))).op

/-- 同じ反転 Čech 添字は弱可縮。零次の対象は収縮の中だけで使う。 -/
lemma cechReverseIndex_isWeaklyContractible : IsWeaklyContractible cechReverseIndex.{u} := by
  let I := AsSmall.{u} SimplexCategoryᵒᵖ
  let L := AsSmall.{u + 1} I
  letI : (AsSmall.up : SimplexCategoryᵒᵖ ⥤ I).IsEquivalence :=
    (AsSmall.equiv (C := SimplexCategoryᵒᵖ)).isEquivalence_functor
  letI : (AsSmall.up : I ⥤ L).IsEquivalence :=
    (AsSmall.equiv (C := I)).isEquivalence_functor
  let v : I := AsSmall.up.obj (Opposite.op ⦋0⦌)
  have hv : IsInitial v := IsInitial.isInitialObj AsSmall.up _ SimplexCategory.isTerminalZero.op
  let w : L := AsSmall.up.obj v
  have hw : IsInitial w := IsInitial.isInitialObj AsSmall.up _ hv
  let T : L ⥤ L := (Functor.const L).obj w
  let h0 : T ⟶ 𝟭 L :=
    { app := fun a => hw.to a
      naturality := by intros; apply hw.hom_ext }
  have hc := nerve_isWeaklyContractible_of_contractionSpan w T h0 (𝟙 T)
  have hd := (isPrecompositionEquivalence_of_iso (nerveAsSmallIso I)).isWeakHomotopyEquivalence.weaklyContractible_iff.mpr hc
  exact hd.op

/-- 同じ弱可縮な反転 Čech 添字上の、指定した頂点を持つ元の定値錐は極限錐。 -/
lemma cechConstantCone_isLimit (E : SSet.{u + 1}) [Quasicategory E] (x : E _⦋0⦌) :
    IsLimitCone (constantDiagramCone cechReverseIndex.{u} E x) :=
  constantDiagramCone_isLimit cechReverseIndex.{u} E cechReverseIndex_isWeaklyContractible x

end SerrePositivity.InfinityCategories.Sheaves
