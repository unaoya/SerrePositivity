module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCoefficientFormula

/-!
概要：指定した底の部分単体上で、係数評価を重み付き図式の成分で計算する。
方針：部分単体の図式の Yoneda 表示と係数評価のパラメータ自然性を組み合わせる。
規約：部分単体への射 r はホーンの面に限定しない。
使われ方：Kerodon §5.3.3（Tag 025W）、最後の面および面の初区間での係数充填の比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：相対図式の指定部分単体上の係数評価は、その最後の成分の終点への輸送。
方針：底の図式と全空間の図式を Yoneda の表示へ直し、係数評価の明示式を適用する。
規約：hτ は部分単体の実際の図式との等式であり、任意の重み付き図式を仮定しない。
使われ方：Kerodon §5.3.3（Tag 025W）、ホーンの最後の面を固定した充填の整合式。 -/
lemma weightedNerveSimplexCoefficient_restriction {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n m : ℕ} (σ : ComposableArrows C n) {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ (Δ[n] : SSet.{u}))
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ)
    (r : (Δ[m] : SSet.{u}) ⟶ T) (α : ⦋m⦌ ⟶ ⦋n⦌)
    (hr : r ≫ b = stdSimplex.map α)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight m ⟶ (SimplexCategory.toCat.map α).toFunctor ⋙ σ ⋙ F)
    (hτ : SSet.yonedaEquiv.symm
      (⟨(SimplexCategory.toCat.map α).toFunctor ⋙ σ, τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F m) = r ≫ a) :
    r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a b h =
      τ.app (Fin.last m) ≫ F.map (σ.map
        (homOfLE (Fin.le_last (α.toOrderHom (Fin.last m))))) := by
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F m := ⟨(SimplexCategory.toCat.map α).toFunctor ⋙ σ, τ⟩
  have hr' : (r ≫ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (r ≫ b) ≫ SSet.yonedaEquiv.symm σ := by
    rw [Category.assoc, h, Category.assoc]
  have hs : SSet.yonedaEquiv.symm s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      stdSimplex.map α ≫ SSet.yonedaEquiv.symm σ :=
    (congrArg (fun q ↦ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) hτ).trans
      (hr'.trans (congrArg (fun q ↦ q ≫ (SSet.yonedaEquiv (X := nerve C) (n := ⦋n⦌)).symm σ) hr))
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ (r ≫ a) (r ≫ b) hr' :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_precomp F σ a b h r hr').symm
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ (SSet.yonedaEquiv.symm s) (stdSimplex.map α) hs :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_congr F σ _ _ _ _ hr' hs hτ.symm hr
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_diagram F σ α τ hs

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
