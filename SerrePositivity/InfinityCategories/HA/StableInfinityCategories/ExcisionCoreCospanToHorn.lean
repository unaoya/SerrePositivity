module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanCode
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetClosureRetraction

/-!
概要：比較格子の穿孔 core と元の cospan の実極限を比較する。
方針：固定した初期収縮と標準ホーンの全単体同型を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionCoreCospanToHorn : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanIndex.{u} ⟶
    (horn 2 2 : SSet.{u}) :=
  Subcomplex.lift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanCodeMap (by
    intro n t ht
    obtain ⟨s, rfl⟩ := ht
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanCodeMap_mem s)

lemma excisionCoreCospanToHorn_ι : excisionCoreCospanToHorn.{u} ≫ (horn 2 2).ι =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanCodeMap := rfl

lemma excisionCoreCospanToHorn_mono : Mono excisionCoreCospanToHorn.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b h
  apply CategoryTheory.nerve.ext_of_isThin
  funext k
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanCode_injective
  exact congrArg (fun s : (horn 2 2 : SSet.{u}).obj n ↦
    (stdSimplex.objEquiv s.val).toOrderHom k) h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
