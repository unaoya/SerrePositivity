module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackFunctorComponents

/-!
概要：引き戻し候補と任意の試験単体集合からの関手空間との交換同型。
方針：二射影と実際の path の一致で比較射の二つの合成を恒等と判定する。
規約：これは全関手 ∞ 圏の厳密な同型であり、core の空間の普遍性は別に示す。
使われ方：Cat_∞ の引き戻しの全試験対象に対する普遍性への入力。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}}

/-- 概要：候補への関手空間に入る射は二射影と path 成分で決まる。
方針：uncurry の単射性と候補への射の外延性を使う。
規約：標的 C の quasicategory 性をこの外延性には要求しない。
使われ方：関手空間比較の一方の合成の検証。 -/
lemma catPullbackFunctor_hom_ext (p : A ⟶ C) (q : B ⟶ C) {T K : SSet.{u}}
    {f g : T ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q)}
    (hf : f ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q) = g ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q))
    (hs : f ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q) = g ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q))
    (hh : f ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q) = g ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q)) :
    f = g := by
  apply uncurry_injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullback_hom_ext p q
  · simpa only [uncurry_natural_right] using congrArg uncurry hf
  · simpa only [uncurry_natural_right] using congrArg uncurry hs
  · simpa only [uncurry_natural_right] using congrArg uncurry hh

/-- 概要：関手空間比較の順射と逆射の合成は恒等。
方針：二射影と path の三成分で比較し、交換同型の逆条件を使う。
規約：試験 K の quasicategory 性は不要。
使われ方：比較の厳密な同型性の第一の逆条件。 -/
lemma catPullbackFunctorMap_inv (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap K p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv K p q = 𝟙 _ := by
  apply catPullbackFunctor_hom_ext p q
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap_fst, Category.id_comp]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap_snd, Category.id_comp]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv_path, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap_path,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- 概要：関手空間比較の逆射と順射の合成は恒等。
方針：候補への射の外延性で二射影と path の三成分を比較する。
規約：path 成分の合成も厳密な恒等に戻す。
使われ方：比較の厳密な同型性の第二の逆条件。 -/
lemma catPullbackFunctorInv_map (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv K p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap K p q = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullback_hom_ext ((ihom K).map p) ((ihom K).map q)
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv_fst, Category.id_comp]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv_snd, Category.id_comp]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap_path, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv_path,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

/-- 概要：引き戻し候補は任意の試験単体集合からの関手空間と交換する。
方針：標準比較射と curry した逆射を二つの厳密な逆条件で同型にする。
規約：元の二射影と指定可逆 path を保つ全単体の同型。
使われ方：全試験 ∞ 圏からの関手 core の比較に進むための模型の交換。 -/
def catPullbackFunctorIso (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) [Quasicategory C] :
    (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback ((ihom K).map p) ((ihom K).map q) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorMap K p q
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackFunctorInv K p q
  hom_inv_id := catPullbackFunctorMap_inv K p q
  inv_hom_id := catPullbackFunctorInv_map K p q

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
