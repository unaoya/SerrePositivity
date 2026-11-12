module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveRelativeSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：weighted nerve の相対ホーンの各面を、指定した底の上の重み付き図式にする。
方針：相対可換条件を各面で評価して底を同定し、面の交わりの等式を図式へ移す。
規約：この段階では係数の Kan 性も欠けた面の添字の制限も不要。
使われ方：Kerodon §5.3.3（Tag 025W）、左ホーン充填の最後の係数値の面データの回収。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：相対ホーンの j 面の底の射列は、指定した底の j 面。
方針：相対可換条件をホーンの面で制限して Yoneda 対応に移す。
規約：j は欠ける面 k 以外。
使われ方：Kerodon §5.3.3（Tag 025W）、ホーン面の係数図式の標的を揃える条件。 -/
lemma weightedNerveHornFace_base {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    (SSet.yonedaEquiv (horn.ι k j hj ≫ a)).1 =
      (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (horn.ι k j hj ≫ a)) =
    (nerve C).map (SimplexCategory.δ j).op σ
  rw [← SSet.yonedaEquiv_comp, Category.assoc, ha, ← Category.assoc,
    horn.ι_ι]
  exact (SSet.yonedaEquiv_naturality (SimplexCategory.δ j)
    ((SSet.yonedaEquiv (X := nerve C)).symm σ)).symm.trans
      (congrArg ((nerve C).map (SimplexCategory.δ j).op)
        ((SSet.yonedaEquiv (X := nerve C) (n := ⦋n + 1⦌)).apply_symm_apply σ))

/-- 概要：相対ホーンの j 面の重み付き図式を指定した底の j 面上に表示する。
方針：各面の底の等式に沿って単体の自然変換を同定する。
規約：h の証明の違いには依存しない。
使われ方：Kerodon §5.3.3（Tag 025W）、最後の係数値のホーンの面を作る入力。 -/
def weightedNerveHornFaceDiagram {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶
      (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ ⋙ F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexDiagram F _ (SSet.yonedaEquiv (horn.ι k j hj ≫ a))
    (weightedNerveHornFace_base F σ k a ha j hj)

/-- 概要：正規化した面の図式を元の底と組み直すと元のホーン面の単体になる。
方針：底を指定した単体の図式の回収の往復則を使う。
規約：元のホーンの面そのものとの等式。
使われ方：Kerodon §5.3.3（Tag 025W）、充填した図式の面と既存のホーン面の比較。 -/
lemma weightedNerveHornFaceDiagram_eta {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    (⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
      weightedNerveHornFaceDiagram F σ k a ha j hj⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) =
      SSet.yonedaEquiv (horn.ι k j hj ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexDiagram_eta F _ _ _

/-- 概要：正規化したホーン面は、ホーン内で一致する部分単体上で一致する。
方針：元の面に戻し、ホーン内の射の等式を Yoneda の自然性で移す。
規約：β と γ は同じ次数から二つの面への任意の射。
使われ方：Kerodon §5.3.3（Tag 025W）、最後の係数値の面データの整合性の検査。 -/
lemma weightedNerveHornFaceDiagram_overlap {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n m : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j l : Fin (n + 2)) (hj : j ≠ k) (hl : l ≠ k)
    (β γ : ⦋m⦌ ⟶ ⦋n⦌)
    (h : (stdSimplex.map β : (Δ[m] : SSet.{u}) ⟶ Δ[n]) ≫ horn.ι k j hj =
      stdSimplex.map γ ≫ horn.ι k l hl) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F β
        ⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
          weightedNerveHornFaceDiagram F σ k a ha j hj⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F γ
        ⟨(SimplexCategory.toCat.map (SimplexCategory.δ l)).toFunctor ⋙ σ,
          weightedNerveHornFaceDiagram F σ k a ha l hl⟩ := by
  rw [weightedNerveHornFaceDiagram_eta, weightedNerveHornFaceDiagram_eta]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F).map β.op (SSet.yonedaEquiv (horn.ι k j hj ≫ a)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F).map γ.op (SSet.yonedaEquiv (horn.ι k l hl ≫ a))
  rw [SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_naturality]
  apply congrArg SSet.yonedaEquiv
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun q ↦ q ≫ a) h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
