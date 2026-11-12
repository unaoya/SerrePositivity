module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.FilteredLeftFibrationRelativeDetection

/-!
概要：引き戻し全空間の有限な相対射を、元の三つの値の path 引き戻しで検出する。
方針：共有底への left fibration の相対有限検出を厳密な fiber 同型で移す。
規約：輸送した境界の厳密な等式と元の指定二射へのホモトピーを保持する。
使われ方：一般 coherent な引き戻し比較の弱同値性の相対有限検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：相対有限射は元の一つの頂点の三値の path 引き戻しで厳密な境界を保って検出できる。
方針：全空間の相対検出の境界と充填を、同じ fiber の厳密な同型で運ぶ。
規約：境界射に単射性は要求しない。使われ方：元の値による有限引き戻し比較の検査。 -/
lemma fiberwisePullbackValue_finite_relative_detection {A K E D H B : SSet.{u}}
    [A.Finite] [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]
    (i : A ⟶ K) (a : A ⟶ fiberwiseIntervalPullback p f g)
    (w : K ⟶ continuousKanReplacement.obj (fiberwiseIntervalPullback p f g))
    (h : a ≫ continuousKanReplacementUnit.app _ = i ≫ w) :
    ∃ b : B _⦋0⦌,
      ∃ t : A ⟶ intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
          (vertexFiberMap (g ≫ p) p g rfl b),
      ∃ v : K ⟶ continuousKanReplacement.obj (intervalPullback
          (vertexFiberMap (f ≫ p) p f rfl b) (vertexFiberMap (g ≫ p) p g rfl b)),
        i ≫ v = t ≫ continuousKanReplacementUnit.app _ ∧
        Nonempty (SSet.Homotopy a (t ≫ fiberwisePullbackValueToTotal p f g b)) ∧
        Nonempty (SSet.Homotopy w
          (v ≫ continuousKanReplacement.map (fiberwisePullbackValueToTotal p f g b))) := by
  obtain ⟨b, t, v, hv, ⟨Ht⟩, ⟨Hv⟩⟩ :=
    continuousKanLeftFibration_finite_relative_detection
      (fiberwiseIntervalPullbackProjection p f g) i a w h
  let e := fiberwisePullbackFiberIso p f g b
  have he : e.hom ≫ fiberwisePullbackValueToTotal p f g b =
      vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b := by
    change e.hom ≫ (e.inv ≫ _) = _
    rw [e.hom_inv_id_assoc]
  refine ⟨b, t ≫ e.hom, v ≫ continuousKanReplacement.map e.hom, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hv, Category.assoc, ← continuousKanReplacementUnit.naturality]
    rfl
  · rw [Category.assoc, he]
    exact ⟨Ht⟩
  · rw [Category.assoc, ← CategoryTheory.Functor.map_comp, he]
    exact ⟨Hv⟩

end SerrePositivity.InfinityCategories.F2
