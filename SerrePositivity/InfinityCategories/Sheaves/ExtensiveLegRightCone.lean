module

public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveTerminalComma
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.NerveConeInitialComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialValueCone
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.RightConeTransportPostcomp

/-!
概要：終点を加えた添字への包含の各脚で、元の指定局所右 Kan 錐を初対象の値の錐に戻す。
方針：頂点・図式・各混合辺を比較し、既存の初対象の値の極限性を使う。
規約：HTT 4.3.2 の既存の指定局所錐の係数移送。係数の極限保存性は仮定しない。
使われ方：S1 の有限余積被覆から指定積錐への比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Sheaves
variable (I : Type u) [SmallCategory I]

/-- 各脚での指定恒等余単位の通常の局所錐。 -/
abbrev extensiveLegRightCone (i : I) :=
  (Functor.RightExtension.mk (L := (WithTerminal.incl : I ⥤ WithTerminal I))
    (𝟭 (WithTerminal I)) (𝟙 (WithTerminal.incl : I ⥤ WithTerminal I))).coneAt
      (WithTerminal.of i)

/-- 元の指定全錐は、同じ comma の恒等三角形からの初対象錐そのもの。 -/
lemma extensiveLegRightCone_val (i : I) :
    (nerveCone (extensiveLegRightCone I i)).val =
      nerveInitialCone (extensiveLegComma_isInitial I i) ≫
        nerveMap (StructuredArrow.proj (WithTerminal.of i)
          (WithTerminal.incl : I ⥤ WithTerminal I) ⋙ WithTerminal.incl) := by
  apply nerve_joinPoint_hom_ext
  · rw [nerveCone_point, ← Category.assoc, nerveInitialCone_left]
    rfl
  · rw [(nerveCone (extensiveLegRightCone I i)).property,
      ← Category.assoc, nerveInitialCone_inr, Category.id_comp]
  · intro a
    rw [nerveCone_leg, NatTrans.comp_app_apply, nerveInitialCone_leg, nerveMap_app_mk₁]
    congr 1
    change a.hom ≫ 𝟙 _ = WithTerminal.incl.map ((extensiveLegComma_isInitial I i).to a).right
    rw [Category.comp_id]
    have hw := StructuredArrow.w ((extensiveLegComma_isInitial I i).to a)
    change (𝟙 (WithTerminal.of i)) ≫
      WithTerminal.incl.map ((extensiveLegComma_isInitial I i).to a).right = a.hom at hw
    simpa only [Category.id_comp] using hw.symm

/-- 任意の準圏値係数でも、各脚での同じ局所錐は極限。 -/
lemma extensiveLegRightCone_postcomp_isLimit {E : SSet.{u}} [Quasicategory E]
    (H : nerve (WithTerminal I) ⟶ E) (i : I) :
    IsLimitCone ((nerveCone (extensiveLegRightCone I i)).postcomp H) := by
  have h := initialValueCone_isLimit (extensiveLegComma_isInitial I i)
    (nerveMap (StructuredArrow.proj (WithTerminal.of i)
      (WithTerminal.incl : I ⥤ WithTerminal I) ⋙ WithTerminal.incl) ≫ H)
  apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).mp h
  change nerveInitialCone _ ≫ _ = (nerveCone (extensiveLegRightCone I i)).val ≫ H
  rw [extensiveLegRightCone_val, Category.assoc]

end SerrePositivity.InfinityCategories.Sheaves
