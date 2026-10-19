module

public import SerrePositivity.InfinityCategories.F1B.KanConeFunctorFiber

/-!
概要：通常の錐の圏と拡張関手の fiber の圏を同値にする。
方針：充満忠実性と対象上の全射性を合わせる。
規約：同じ宇宙の小さい圏と単体集合を扱う。
使われ方：B5 の通常の錐と native な錐の族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：錐から関手の fiber への指定関手は圏同値。
方針：充満忠実性と対象上の全射性を合わせる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
instance kanConeFiberFunctor_isEquivalence : (kanConeFiberFunctor (F := F)).IsEquivalence := by
  refine { faithful := (kanConeFiberFunctor_fullyFaithful (F := F)).faithful
           full := (kanConeFiberFunctor_fullyFaithful (F := F)).full
           essSurj := ⟨fun G ↦ ?_⟩ }
  obtain ⟨c, hc⟩ := kanConeFiberFunctor_obj_surjective (F := F) G
  exact ⟨c, ⟨eqToIso hc⟩⟩

/-- 概要：通常の錐の圏と固定図式上の拡張関手の圏の指定同値。
方針：充満忠実性と対象上の全射性を合わせる。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def kanConeFiberEquivalence :
    Cone F ≌ Functor.Fiber (kanConeRestrictionFunctor (I := I) (C := C)) F :=
  (kanConeFiberFunctor (F := F)).asEquivalence

end SerrePositivity.InfinityCategories.F1B
