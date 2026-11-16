module

public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveCofanRestriction
public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveCofanCover

/-!
概要：元の extensive 層は、空族を含む同じ指定有限積錐を極限錐へ送る。
方針：元の fan を脚を保って cofan に戻し、同じ生成篩の降下を使う。
  文献対応：HTT 6.2.2.6 の extensive 位相での層条件。
規約：有限 Type u のすべての指定 fan を扱い、空族を省略しない。
使われ方：S1 の元の有限積保存の判定。逆向きの位相への接続は別途示す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 有限族の元の指定積錐を極限錐へ送る。空族も含む。
型の正本は drafts/Sheaves/SheafCondition の同名の定義。 -/
def PreservesFiniteProductsOnSite (F : Presheaf C E) : Prop :=
  ∀ (ι : Type u) [Finite ι] (B : ι → Cᵒᵖ) (c : Fan B), Nonempty (IsLimit c) →
    IsLimitCone (mapJoinCone F
      (SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1}
        (nerveCone c)))

/-- 元の fan を同じ脚の双対で往復しても、nerve の全錐の射を保つ。 -/
lemma cofanToOppositeFan_fanToUnopCofan_val {ι : Type u} {B : ι → Cᵒᵖ} (c : Fan B) :
    (nerveCone (cofanToOppositeFan (fanToUnopCofan c))).val = (nerveCone c).val := by
  apply nerve_joinPoint_hom_ext
  · rw [nerveCone_point, nerveCone_point]
    rfl
  · rw [(nerveCone (cofanToOppositeFan (fanToUnopCofan c))).property,
      (nerveCone c).property]
  · intro i
    rw [nerveCone_leg, nerveCone_leg]
    rfl

/-- 同じ双対の往復の全射は、元の係数・宇宙移送の後も一致する。 -/
lemma cofanToOppositeFan_fanToUnopCofan_image_val {ι : Type u} {B : ι → Cᵒᵖ}
    (F : Presheaf C E) (c : Fan B) :
    (((nerveCone (cofanToOppositeFan (fanToUnopCofan c))).ulift).postcomp F).val =
      (((nerveCone c).ulift).postcomp F).val := by
  change ((uliftConeShapeIso (nerve (Discrete ι)) 0).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveCone (cofanToOppositeFan (fanToUnopCofan c))).val) ≫ F = _
  rw [cofanToOppositeFan_fanToUnopCofan_val]
  rfl

private def emptyDiscreteShape_isInitial (ι : Type u) [IsEmpty ι] :
    IsInitial ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete ι))) :=
  SSet.isInitialOfNotNonempty (by
    rintro ⟨a⟩
    exact isEmptyElim (nerveEquiv a.down).as)

/-- 元の extensive 層は、空族を含む元の指定有限積錐を極限錐へ送る。 -/
lemma IsSheaf.preservesFiniteProductsOnSite [FinitaryExtensive C]
    (F : Presheaf C E) (hF : IsSheaf (extensiveTopology C) F) :
    PreservesFiniteProductsOnSite F := by
  classical
  intro ι _ B c ⟨hc⟩
  let k := fanToUnopCofan c
  have hk : IsColimit k := fanToUnopCofan_isColimit c hc
  have hs := hF k.pt (cofanGeneratedSieve k) (cofanGeneratedSieve_mem_extensiveTopology k hk)
  by_cases hi : Nonempty ι
  · letI := hi
    have hf := (cofanRestriction_isLimit_iff F
      (isTerminal_initial_of_isSheaf_extensive F hF) k hk).mp hs
    exact (isLimitCone_iff_of_cone_val_eq _ _
      (cofanToOppositeFan_fanToUnopCofan_image_val F c)).mp hf
  · letI : IsEmpty ι := not_nonempty_iff.mp hi
    rw [cofanGeneratedSieve_eq_bot] at hs
    have ht := (restrictionCone_bot_isLimit_iff F k.pt).mp hs
    apply (isLimitCone_iff_terminal_of_initialShape (emptyDiscreteShape_isInitial ι) _).mpr
    change IsTerminalVertex ((mapJoinCone F (nerveCone c).ulift).vertex)
    rw [mapJoinCone_vertex,
      SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift_vertex,
      nerveCone_vertex]
    exact ht

end SerrePositivity.InfinityCategories.Sheaves
