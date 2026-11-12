module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeCompositionSections

/-!
概要：二重底変換と直接底変換の元の全空間を、同じ射影を保つ厳密な同型で比較する。
方針：貼り合わせた pullback の普遍性と、元の cocartesian 辺の反映を使う。
規約：section の分類像だけでなく、元の全空間とその全ての辺を保持する。
使われ方：二次元 Segal 制限の共有頂点で、二重引き戻しを直接引き戻しへ移す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  {E : SSet.{u}} (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (l : A ⥤ D) (k : D ⥤ C)

/-- 元の二重 pullback と直接 pullback の、同じ普遍性による全空間の同型。 -/
def cocartesianBaseChangeNativeAssociativity :
    pullback (nerveMap l) (pullback.fst (nerveMap k) p) ≅
      pullback (nerveMap (l ⋙ k)) p :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeComposite_isPullback p l k).flip.isoPullback

/-- 同じ同型は、新しい底への元の射影を保持する。 -/
lemma cocartesianBaseChangeNativeAssociativity_hom_fst :
    (cocartesianBaseChangeNativeAssociativity p l k).hom ≫
      pullback.fst (nerveMap (l ⋙ k)) p =
    pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeComposite_isPullback p l k).flip.isoPullback_hom_fst

/-- 同じ同型は、元の全空間への二回の射影を保持する。 -/
lemma cocartesianBaseChangeNativeAssociativity_hom_snd :
    (cocartesianBaseChangeNativeAssociativity p l k).hom ≫
      pullback.snd (nerveMap (l ⋙ k)) p =
    pullback.snd (nerveMap l) (pullback.fst (nerveMap k) p) ≫ pullback.snd (nerveMap k) p :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeComposite_isPullback p l k).flip.isoPullback_hom_snd

/-- 逆同型も、元の全空間への同じ射影を保持する。 -/
lemma cocartesianBaseChangeNativeAssociativity_inv_snd :
    (cocartesianBaseChangeNativeAssociativity p l k).inv ≫
      pullback.snd (nerveMap l) (pullback.fst (nerveMap k) p) ≫ pullback.snd (nerveMap k) p =
    pullback.snd (nerveMap (l ⋙ k)) p := by
  rw [← cocartesianBaseChangeNativeAssociativity_hom_snd p l k]
  simp only [Iso.inv_hom_id_assoc]

/-- 元の同じ全空間の結合同型は、全ての cocartesian 辺を保つ。 -/
lemma cocartesianBaseChangeNativeAssociativity_preserves :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p))
      (pullback.fst (nerveMap (l ⋙ k)) p)
      (cocartesianBaseChangeNativeAssociativity p l k).hom := by
  intro e he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_isPullback_iff p
    (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip _).mpr
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_isPullback_iff p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeComposite_isPullback p l k) e).mp he
  have hs := congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e)
    (cocartesianBaseChangeNativeAssociativity_hom_snd p l k)
  exact hs ▸ h

/-- 元の同じ逆結合同型も、全ての cocartesian 辺を保つ。 -/
lemma cocartesianBaseChangeNativeAssociativity_inv_preserves :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges (pullback.fst (nerveMap (l ⋙ k)) p)
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p))
      (cocartesianBaseChangeNativeAssociativity p l k).inv := by
  intro e he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_isPullback_iff p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeComposite_isPullback p l k) _).mpr
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_isPullback_iff p
    (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip e).mp he
  have hs := congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e)
    (cocartesianBaseChangeNativeAssociativity_inv_snd p l k)
  exact hs ▸ h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
