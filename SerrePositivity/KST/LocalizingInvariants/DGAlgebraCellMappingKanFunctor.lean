module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingKan
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits

/-!
概要：cell 源の実乗法的写像を Kan 複体値の関手に束ねる。
方針：元の全標的射を使い、忘却後の元の極限保存で通常の Kan 錐を検証する。
規約：局所化後の導来写像空間との比較はここでは主張しない。
使われ方：元の Postnikov 錐の実 Kan 模型と、空間の極限への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

def multiplicativeCellMappingKanFunctor : Mon (Complex R) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj B := ⟨multiplicativeMappingSimplices R (cellResolution R A) B, inferInstance⟩
  map f := multiplicativeMappingPostcompose R (cellResolution R A) f
  map_id B := (multiplicativeMappingFunctor R (cellResolution R A)).map_id B
  map_comp f g := (multiplicativeMappingFunctor R (cellResolution R A)).map_comp f g

lemma multiplicativeCellMappingKanFunctor_forget :
    multiplicativeCellMappingKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget =
      multiplicativeMappingFunctor R (cellResolution R A) := rfl

def multiplicativeCellMappingKanCone_isLimit {J : Type u} [SmallCategory J]
    (F : J ⥤ Mon (Complex R)) (c : Cone F) (hc : IsLimit c) :
    IsLimit ((multiplicativeCellMappingKanFunctor R A).mapCone c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectCone_isLimit_of_forget
  change IsLimit ((multiplicativeCellMappingKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).mapCone c)
  rw [multiplicativeCellMappingKanFunctor_forget]
  exact isLimitOfPreserves (multiplicativeMappingFunctor R (cellResolution R A)) hc

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
