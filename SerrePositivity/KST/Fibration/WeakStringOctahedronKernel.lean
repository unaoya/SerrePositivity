module
public import SerrePositivity.KST.Fibration.WeakStringOctahedronFamilies

/-! # 八面体の比較列の核値性

共通 cofiber 関手の回収と関手圏内の全図式の同型を使い、
八面体の最後の実 cofiber 列の三頂点が商で零になることを証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 八面体の最後の列の始点は、元の第一短辺の核値 cofiber である。 -/
lemma weakStringOctahedronFamily_source_kernel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom (weakStringCategory q n)).map q.hom).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 0 0)) := by
  rw [(weakStringOctahedronFamily q β).last_source]
  exact weakStringCofiberFamily_kernel q _

/-- 八面体の最後の列の中間頂点も、長辺の共通 cofiber との族の同型により核に入る。 -/
lemma weakStringOctahedronFamily_middle_kernel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom (weakStringCategory q n)).map q.hom).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 1 0)) := by
  rw [(weakStringOctahedronFamily q β).last_middle]
  exact (weakStringCofiberFamily_kernel q (SimplexCategory.δ (1 : Fin 3) ≫ β)).of_vertexIso
    ((cofiberFamilyCornerIso (weakStringOctahedronFamily_compositeComparison q β)).map
      ((ihom (weakStringCategory q n)).map q.hom)).symm

/-- 八面体の最後の列の終点も、第二短辺の共通 cofiber との族の同型により核に入る。 -/
lemma weakStringOctahedronFamily_target_kernel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom (weakStringCategory q n)).map q.hom).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (weakStringOctahedronFamily q β).second.rightZeroTriangle.square 1 1)) := by
  rw [(weakStringOctahedronFamily q β).last_target]
  exact (weakStringCofiberFamily_kernel q (SimplexCategory.δ (0 : Fin 3) ≫ β)).of_vertexIso
    ((cofiberFamilyCornerIso (weakStringOctahedronFamily_nextComparison q β)).map
      ((ihom (weakStringCategory q n)).map q.hom)).symm

end SerrePositivity.KST.Fibration
