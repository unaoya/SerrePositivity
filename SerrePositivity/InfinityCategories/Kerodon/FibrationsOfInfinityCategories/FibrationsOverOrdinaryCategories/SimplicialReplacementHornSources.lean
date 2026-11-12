module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementSourceCoefficient
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：simplicial replacement の相対ホーンの始点を保つ面の係数表示。
方針：各面の底を指定した射列の面に同定し、零以外の面を同じ始点の係数値へ輸送する。
規約：係数の Kan 性はこの表示には要求しない。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、§5.3.5（Tag 037H）、相対ホーンの係数による充填。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：零以外の面の単調写像は始点を保つ。
方針：欠ける頂点を後者で表示し、succAbove の零での値を計算する。
規約：零次元の面も含む。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、係数の標的が変わらない面の判定。 -/
lemma simplexFace_zero_of_ne_zero {n : ℕ} (j : Fin (n + 2)) (hj : j ≠ 0) :
    (SimplexCategory.δ j).toOrderHom 0 = 0 := by
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero hj
  exact Fin.succ_succAbove_zero j

/-- 概要：相対ホーンの各面の底は指定した底の射列の面となる。
方針：底上の可換性をホーンの面で制限し、Yoneda の自然性で単体へ移す。
規約：欠ける面以外の面を扱う。
使われ方：Kerodon §5.3.5（Tag 037H）、面の係数の始点の同定。 -/
lemma simplicialReplacementHornFace_base
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    (SSet.yonedaEquiv (horn.ι k j hj ≫ a)).1 =
      (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (horn.ι k j hj ≫ a)) =
    (nerve C).map (SimplexCategory.δ j).op σ
  rw [← SSet.yonedaEquiv_comp, Category.assoc, ha, ← Category.assoc, horn.ι_ι]
  exact (SSet.yonedaEquiv_naturality (SimplexCategory.δ j)
    ((SSet.yonedaEquiv (X := nerve C)).symm σ)).symm.trans
      (congrArg ((nerve C).map (SimplexCategory.δ j).op)
        ((SSet.yonedaEquiv (X := nerve C) (n := ⦋n + 1⦌)).apply_symm_apply σ))

/-- 概要：零以外のホーン面の係数の始点は元の射列の始点となる。
方針：面の底の公式の始点を取り、面の単調写像の零での値を使う。
規約：欠ける面 k と零の両方を避ける面 j を扱う。
使われ方：Kerodon §5.3.5（Tag 037H）、係数のホーンの標的を揃える等式。 -/
lemma simplicialReplacementHornFace_start
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) (hj0 : j ≠ 0) :
    (SSet.yonedaEquiv (horn.ι k j hj ≫ a)).1.obj 0 = σ.obj 0 :=
  (congrArg (fun τ : ComposableArrows C n ↦ τ.obj 0)
    (simplicialReplacementHornFace_base F σ k a ha j hj)).trans
      (congrArg σ.obj (simplexFace_zero_of_ne_zero j hj0))

/-- 概要：相対ホーンの零以外の面の係数を元の始点の値で表示する。
方針：面の始点の同定を係数単体の輸送に使う。
規約：係数の充填性や底の射列の単射性は要求しない。
使われ方：Kerodon §5.3.5（Tag 037H）、始点の係数値の中に作るホーンの各面。 -/
def simplicialReplacementHornSourceFace
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) (hj0 : j ≠ 0) :
    (Δ[n] : SSet.{u}) ⟶ F.obj (σ.obj 0) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSourceCoefficient F (SSet.yonedaEquiv (horn.ι k j hj ≫ a)) (σ.obj 0)
    (simplicialReplacementHornFace_start F σ k a ha j hj hj0)

/-- 概要：零以外のホーン面の係数は始点を保つ交わりで一致する。
方針：ホーン内の一致を Yoneda で制限した単体の一致へ移し、始点の係数の自然性を使う。
規約：二つの部分単体の制限は両方とも始点を保つ。
使われ方：Kerodon §5.3.5（Tag 037H）、係数値のホーンの面の整合性。 -/
lemma simplicialReplacementHornSourceFace_overlap
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n m : ℕ}
    (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j l : Fin (n + 2)) (hj : j ≠ k) (hl : l ≠ k) (hj0 : j ≠ 0) (hl0 : l ≠ 0)
    (β γ : ⦋m⦌ ⟶ ⦋n⦌) (hβ : β.toOrderHom 0 = 0) (hγ : γ.toOrderHom 0 = 0)
    (he : (stdSimplex.map β : (Δ[m] : SSet.{u}) ⟶ Δ[n]) ≫ (horn.ι k j hj ≫ a) =
      stdSimplex.map γ ≫ (horn.ι k l hl ≫ a)) :
    stdSimplex.map β ≫ simplicialReplacementHornSourceFace F σ k a ha j hj hj0 =
      stdSimplex.map γ ≫ simplicialReplacementHornSourceFace F σ k a ha l hl hl0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSourceCoefficient_overlap F β γ hβ hγ
    (SSet.yonedaEquiv (horn.ι k j hj ≫ a)) (SSet.yonedaEquiv (horn.ι k l hl ≫ a))
    (σ.obj 0) (simplicialReplacementHornFace_start F σ k a ha j hj hj0)
    (simplicialReplacementHornFace_start F σ k a ha l hl hl0)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F).map β.op (SSet.yonedaEquiv (horn.ι k j hj ≫ a)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F).map γ.op (SSet.yonedaEquiv (horn.ι k l hl ≫ a))
  rw [SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_naturality]
  exact congrArg SSet.yonedaEquiv he

/-- 概要：零番目の相対ホーンの面の係数は同じ係数値のホーンの整合条件を満たす。
方針：指定された面の交わりが始点を保つことを確認して、係数の交わりの一致を適用する。
規約：一次ホーンの整合条件は自明。
使われ方：Kerodon §5.3.5（Tag 037H）、Kan 係数値での零番目のホーンの充填。 -/
lemma simplicialReplacementHornSourceFace_zero_isCompatible
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1))
    (a : (horn (n + 1) 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      (horn (n + 1) 0).ι ≫ SSet.yonedaEquiv.symm σ) :
    horn.IsCompatible (fun j hj ↦ simplicialReplacementHornSourceFace F σ 0 a ha j hj hj) := by
  cases n with
  | zero => trivial
  | succ n =>
    rw [horn.isCompatible_iff]
    intro j l hj hl hjl
    have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun h ↦ hj (Fin.ext h))
    have hpred : l.pred (Fin.ne_zero_of_lt hjl) ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_pred, Fin.val_zero] at hv
      change j.val < l.val at hjl
      omega
    have hcast : j.castPred (Fin.ne_last_of_lt hjl) ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = 0 at hv
      omega
    exact simplicialReplacementHornSourceFace_overlap F σ 0 a ha j l hj hl hj hl
      (SimplexCategory.δ (l.pred (Fin.ne_zero_of_lt hjl)))
      (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjl)))
      (simplexFace_zero_of_ne_zero _ hpred) (simplexFace_zero_of_ne_zero _ hcast)
      ((horn.IsCompatible.of_hom a).δ_pred_comp j l hj hl hjl)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
