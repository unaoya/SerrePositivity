module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanCode
public import SerrePositivity.InfinityCategories.F2.LimitConeExtension
public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Core.LeftPrism
public import SerrePositivity.InfinityCategories.Core.PrismFilling
public import SerrePositivity.InfinityCategories.Stable.PosetClosureRetraction

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
namespace SerrePositivity.InfinityCategories

def excisionCoreCospanToHorn : nerve ExcisionCoreCospanIndex.{u} ⟶
    (horn 2 2 : SSet.{u}) :=
  Subcomplex.lift excisionCoreCospanCodeMap (by
    intro n t ht
    obtain ⟨s, rfl⟩ := ht
    exact excisionCoreCospanCodeMap_mem s)

lemma excisionCoreCospanToHorn_ι : excisionCoreCospanToHorn.{u} ≫ (horn 2 2).ι =
    excisionCoreCospanCodeMap := rfl

lemma excisionCoreCospanToHorn_mono : Mono excisionCoreCospanToHorn.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b h
  apply CategoryTheory.nerve.ext_of_isThin
  funext k
  apply excisionCoreCospanCode_injective
  exact congrArg (fun s : (horn 2 2 : SSet.{u}).obj n ↦
    (stdSimplex.objEquiv s.val).toOrderHom k) h

end SerrePositivity.InfinityCategories
