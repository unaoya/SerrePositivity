module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction

/-!
概要：エピ射の前合成の単射性。
方針：反変内部 Hom の右随伴が反対圏の単射を保つことを使う。
規約：標的の quasicategory 性は不要。
使われ方：Kerodon §4.6.4（Tag 01KE） の slice 対角射の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：エピ射で前合成すると関手単体集合の単射になる。
方針：反変内部 Hom の自己随伴と右随伴の単射保存を使う。
規約：任意の単体集合の射と任意の標的を扱う。
使われ方：Kerodon §4.6.4（Tag 01KE） の比較の単射性。 -/
instance mono_pre_of_epi {A B : SSet.{u}} (i : A ⟶ B) [Epi i] (X : SSet.{u}) :
    Mono ((pre i).app X) := by
  have : (internalHom.flip.obj X).IsRightAdjoint := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipAdjunction X).isRightAdjoint
  exact (internalHom.flip.obj X).map_mono i.op

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
