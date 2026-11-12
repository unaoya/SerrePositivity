module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePunctured
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

abbrev ExcisionCoreCospanIndex :=
  {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePuncturedIndex.{u} // _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCoreCospan p}

def excisionCoreCospanCode : ExcisionCoreCospanIndex.{u} →o Fin 3 where
  toFun p := ⟨if p.val.val.val.val.down.val.2.val = 0 then 0
    else if p.val.val.val.val.down.val.1.val = 0 then 1 else 2, by split_ifs <;> omega⟩
  monotone' := by
    intro p q h
    have hp := p.property
    have hq := q.property
    have hp0 := p.val.property
    have hq0 := q.val.property
    change p.val.val.val.val.down.val.1.val ≤ 1 ∧ p.val.val.val.val.down.val.2.val ≤ 1 at hp
    change q.val.val.val.val.down.val.1.val ≤ 1 ∧ q.val.val.val.val.down.val.2.val ≤ 1 at hq
    change 1 ≤ p.val.val.val.val.down.val.1.val + p.val.val.val.val.down.val.2.val at hp0
    change 1 ≤ q.val.val.val.val.down.val.1.val + q.val.val.val.val.down.val.2.val at hq0
    have hx := h.1
    have hy := h.2
    change p.val.val.val.val.down.val.1.val ≤ q.val.val.val.val.down.val.1.val at hx
    change p.val.val.val.val.down.val.2.val ≤ q.val.val.val.val.down.val.2.val at hy
    change (if p.val.val.val.val.down.val.2.val = 0 then 0
      else if p.val.val.val.val.down.val.1.val = 0 then 1 else 2) ≤
      (if q.val.val.val.val.down.val.2.val = 0 then 0
        else if q.val.val.val.val.down.val.1.val = 0 then 1 else 2)
    split_ifs <;> omega

lemma excisionCoreCospanCode_injective :
    Function.Injective (excisionCoreCospanCode.{u}) := by
  intro p q h
  have hp := p.property
  have hq := q.property
  have hp0 := p.val.property
  have hq0 := q.val.property
  change p.val.val.val.val.down.val.1.val ≤ 1 ∧ p.val.val.val.val.down.val.2.val ≤ 1 at hp
  change q.val.val.val.val.down.val.1.val ≤ 1 ∧ q.val.val.val.val.down.val.2.val ≤ 1 at hq
  change 1 ≤ p.val.val.val.val.down.val.1.val + p.val.val.val.val.down.val.2.val at hp0
  change 1 ≤ q.val.val.val.val.down.val.1.val + q.val.val.val.val.down.val.2.val at hq0
  have hc := congrArg Fin.val h
  change (if p.val.val.val.val.down.val.2.val = 0 then 0
    else if p.val.val.val.val.down.val.1.val = 0 then 1 else 2) =
    (if q.val.val.val.val.down.val.2.val = 0 then 0
      else if q.val.val.val.val.down.val.1.val = 0 then 1 else 2) at hc
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> split_ifs at hc <;> omega

def excisionCoreCospanCodeMap : nerve ExcisionCoreCospanIndex.{u} ⟶ Δ[2] where
  app n := ↾fun s ↦ stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    (excisionCoreCospanCode.comp (⟨s.obj, s.monotone⟩ : Fin (n.unop.len + 1) →o _)))
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro i
    rfl

lemma excisionCoreCospanCodeMap_mem {n : SimplexCategoryᵒᵖ}
    (s : (nerve ExcisionCoreCospanIndex.{u}).obj n) :
    excisionCoreCospanCodeMap.app n s ∈ (horn 2 2).obj n := by
  apply (mem_horn_iff_notMem_range _ (2 : Fin 3)).mpr
  by_cases hy : (s.obj 0).val.val.val.val.down.val.2.val = 0
  · refine ⟨1, by decide, ?_⟩
    rintro ⟨k, hk⟩
    have hp := (s.obj 0).val.property
    change 1 ≤ (s.obj 0).val.val.val.val.down.val.1.val +
      (s.obj 0).val.val.val.val.down.val.2.val at hp
    have hx := (s.monotone (Fin.zero_le k)).1
    change (s.obj 0).val.val.val.val.down.val.1.val ≤
      (s.obj k).val.val.val.val.down.val.1.val at hx
    change excisionCoreCospanCode (s.obj k) = (1 : Fin 3) at hk
    have hc := congrArg Fin.val hk
    change (if (s.obj k).val.val.val.val.down.val.2.val = 0 then 0
      else if (s.obj k).val.val.val.val.down.val.1.val = 0 then 1 else 2) = 1 at hc
    split_ifs at hc <;> omega
  · refine ⟨0, by decide, ?_⟩
    rintro ⟨k, hk⟩
    have hle := (s.monotone (Fin.zero_le k)).2
    change (s.obj 0).val.val.val.val.down.val.2.val ≤
      (s.obj k).val.val.val.val.down.val.2.val at hle
    change excisionCoreCospanCode (s.obj k) = (0 : Fin 3) at hk
    have hc := congrArg Fin.val hk
    change (if (s.obj k).val.val.val.val.down.val.2.val = 0 then 0
      else if (s.obj k).val.val.val.val.down.val.1.val = 0 then 1 else 2) = 0 at hc
    (split_ifs at hc; omega)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
