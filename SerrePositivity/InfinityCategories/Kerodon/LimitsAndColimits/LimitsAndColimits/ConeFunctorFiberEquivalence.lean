module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeFunctorFiber

/-!
概要：通常の錐の圏と拡張関手の fiber の圏を同値にする。
方針：充満忠実性と対象上の全射性を合わせる。
規約：同じ宇宙の小さい圏と単体集合を扱う。
使われ方：B5 の通常の錐と native な錐の族の比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：錐から関手の fiber への指定関手は圏同値。
方針：充満忠実性と対象上の全射性を合わせる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
instance coneFiberFunctor_isEquivalence : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFiberFunctor (F := F)).IsEquivalence := by
  refine { faithful := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFiberFunctor_fullyFaithful (F := F)).faithful
           full := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFiberFunctor_fullyFaithful (F := F)).full
           essSurj := ⟨fun G ↦ ?_⟩ }
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFiberFunctor_obj_surjective (F := F) G
  exact ⟨c, ⟨eqToIso hc⟩⟩

/-- 概要：通常の錐の圏と固定図式上の拡張関手の圏の指定同値。
方針：充満忠実性と対象上の全射性を合わせる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def coneFiberEquivalence :
    Cone F ≌ Functor.Fiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneRestrictionFunctor (I := I) (C := C)) F :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFiberFunctor (F := F)).asEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
