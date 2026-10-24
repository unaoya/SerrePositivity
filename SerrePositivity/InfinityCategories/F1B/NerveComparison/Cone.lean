module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinFaces
public import SerrePositivity.InfinityCategories.Core.Limit
public import Mathlib.CategoryTheory.Limits.ConeCategory

/-!
概要：通常の錐を元の nerve の join の錐へ写す。
方針：WithInitial の拡張関手と点と nerve の join の既存同型を使う。
規約：比較射の構成と普遍性の証明を区別する。
使われ方：B5 の pointwise Kan の古典比較。
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

/-- 概要：通常の錐を新しい始点を付加した関手へ拡張する。
方針：WithInitial.lift に錐の成分と自然性を渡す。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def coneWithInitialFunctor (c : Cone F) : WithInitial I ⥤ C :=
  WithInitial.lift F c.π.app (fun _i _j f ↦ c.w f)

/-- 概要：通常の錐を元の nerve の join の錐へ移す。
方針：既存の join の同型と拡張関手の nerve を合成する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def nerveCone (c : Cone F) : JoinCone (nerveMap F) :=
  ⟨(HomotopyLimits.initialJoinNerveIso I).hom ≫ nerveMap (coneWithInitialFunctor c), by
    rw [← Category.assoc]
    change (joinInr (Δ[0] : SSet.{u}) (nerve I) ≫ HomotopyLimits.initialJoinNerveMap I) ≫ _ = _
    rw [HomotopyLimits.joinInr_initialJoinNerveMap]
    rfl⟩

/-- 概要：移した錐の頂点は元の錐の頂点の nerve に等しい。
方針：join の左包含の公式で始点を評価する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma nerveCone_vertex (c : Cone F) : (nerveCone c).vertex = nerveVertex c.pt := by
  rw [JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) (nerve I) ≫
    (HomotopyLimits.initialJoinNerveMap I ≫ nerveMap (coneWithInitialFunctor c))) = _
  rw [← Category.assoc, HomotopyLimits.joinInl_initialJoinNerveMap]
  exact ComposableArrows.ext₀ rfl

/-- 概要：拡張関手の始点からの射は元の錐の成分。
方針：WithInitial.lift の射への作用を読む。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma coneWithInitialFunctor_homTo (c : Cone F) (i : I) :
    (coneWithInitialFunctor c).map (WithInitial.homTo i) = c.π.app i := rfl

end SerrePositivity.InfinityCategories.F1B
