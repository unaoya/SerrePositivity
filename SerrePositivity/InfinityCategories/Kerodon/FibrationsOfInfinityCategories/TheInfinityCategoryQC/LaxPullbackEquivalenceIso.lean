module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackEquivalenceComparison

/-!
概要：通常の引き戻しと同値矢印の全部分複体との厳密な同型。
方針：二射影と指定 path の三成分で往復を恒等と判定する。
規約：任意の単体集合間の二射で成立する同型として証明する。
使われ方：Tamme §1 Remark 7 の全部分 ∞ 圏による表示。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}}

/-- 概要：順向き比較射は元の指定可逆 path を保つ。
方針：可逆 path の包含の単射性と矢印成分の一致を使う。
規約：同値類だけでなく元の全次数の path を比較する。
使われ方：比較同型の逆条件と指定 path の保持。 -/
lemma catPullbackToEquivalenceSubcomplex_path (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToEquivalenceSubcomplex p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalencePath p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    ((ihom (Δ[1] : SSet.{u})).obj C) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex).ι).1
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalencePath p q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι C = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalencePath_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToEquivalenceSubcomplex_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_arrow]
  rfl

/-- 概要：通常の引き戻しと同値矢印の全部分複体は厳密に同型。
方針：順射と逆射の合成を三成分の外延性で判定する。
規約：この段階では元の三圏の quasicategory 性も不要。
使われ方：Tamme §1 Remark 7 の具体的な比較同型。 -/
def catPullbackEquivalenceSubcomplexIso (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q ≅ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalenceSubcomplex p q : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToEquivalenceSubcomplex p q
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.equivalenceSubcomplexToCatPullback p q
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullback_hom_ext p q
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.equivalenceSubcomplexToCatPullback_fst,
        ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToEquivalenceSubcomplex_ι,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_fst, Category.id_comp]
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.equivalenceSubcomplexToCatPullback_snd,
        ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToEquivalenceSubcomplex_ι,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_snd, Category.id_comp]
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.equivalenceSubcomplexToCatPullback_path,
        catPullbackToEquivalenceSubcomplex_path, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsLaxEquivalenceVertex p q)).ι).1
    change (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToEquivalenceSubcomplex p q) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalenceSubcomplex p q).ι = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToEquivalenceSubcomplex_ι, Category.id_comp]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullback_hom_ext p q
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_arrow, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.equivalenceSubcomplexToCatPullback_path, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalencePath_ι]
      rfl
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.equivalenceSubcomplexToCatPullback_fst]
      rfl
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.equivalenceSubcomplexToCatPullback_snd]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
