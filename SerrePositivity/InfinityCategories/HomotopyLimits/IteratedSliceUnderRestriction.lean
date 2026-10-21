module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IteratedSliceUnderIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionBaseEvaluation

/-!
概要：展開した図式から元の左因子への制限を反復 coslice の射影に同定する。
方針：元の固定図式と可変終点を同じ join の再結合で保持する。
規約：充填条件を追加仮定しない。使われ方：HTT 5.5.4 の局所同値の pushout 保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {K L X A A' : SSet.{u}} {p : K ⟶ X} (q : L ⟶ sliceUnder p)

/-- 元の左因子へ制限し、固定条件で終域を元の coslice に移す。 -/
def uncurriedSliceUnderRestriction : sliceUnder (sliceUnderUncurry q) ⟶ sliceUnder p :=
  sliceUnderRestrict (sliceUnderUncurry q) (joinInl K L) ≫
    eqToHom (congrArg (fun f : K ⟶ X ↦ sliceUnder f) (sliceUnderUncurry_fixed q))

/-- 元の図式への制限は左因子の包含への前合成として展開される。 -/
lemma uncurriedSliceUnderRestriction_uncurry (s : A ⟶ sliceUnder (sliceUnderUncurry q)) :
    sliceUnderUncurry (s ≫ uncurriedSliceUnderRestriction q) =
      joinMap (joinInl K L) (𝟙 A) ≫ sliceUnderUncurry s := by
  rw [uncurriedSliceUnderRestriction, ← Category.assoc,
    sliceUnderUncurry_eqToHom (sliceUnderUncurry_fixed q),
    sliceUnderUncurry_restrict]

/-- 順方向の族の制限は元の反復 coslice の射影。 -/
lemma iteratedSliceUnderForwardFamily_restriction (s : A ⟶ sliceUnder q) :
    iteratedSliceUnderForwardFamily q s ≫ uncurriedSliceUnderRestriction q =
      s ≫ sliceUnderProjection q := by
  apply sliceUnderUncurry_injective p
  rw [uncurriedSliceUnderRestriction_uncurry, iteratedSliceUnderForwardFamily_uncurry,
    ← Category.assoc, joinAssociator_outerPair, ← sliceUnderUncurry_precomp,
    sliceUnderUncurry_projection]

/-- 反復 coslice の同型は元の図式への制限と射影を対応させる。 -/
lemma iteratedSliceUnderIso_restriction :
    (iteratedSliceUnderIso q).hom ≫ uncurriedSliceUnderRestriction q = sliceUnderProjection q := by
  simpa only [Category.id_comp, iteratedSliceUnderIso, iteratedSliceUnderMap] using
    iteratedSliceUnderForwardFamily_restriction q (𝟙 (sliceUnder q))

/-- 元の左因子への制限は可変終点の射影を保つ。 -/
lemma uncurriedSliceUnderRestriction_projection :
    uncurriedSliceUnderRestriction q ≫ sliceUnderProjection p =
      sliceUnderProjection (sliceUnderUncurry q) := by
  apply (cancel_epi (iteratedSliceUnderIso q).hom).1
  rw [← Category.assoc, iteratedSliceUnderIso_restriction]
  exact (iteratedSliceUnderIso_projection q).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
