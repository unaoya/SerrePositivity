module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.UniverseConeTransport

/-!
概要：実際の相対因子化から次の閉前置段を構成する。
方針：全余錐を順序余錐形状へ戻し、現在成分だけ表示添字を延長する。
規約：元の厳密前置段と両表示添字を全単体上で保持する。
使われ方：長さ κ₀ の相対交互塔の実際の再帰段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

variable {κ : Cardinal.{u}} {B : SSet.{u + 1}}
  {x : (Δ[0] : SSet.{u + 1}) ⟶ B} {I : Fin 2 → SSet.{u}}
  {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}

/-- 概要：選んだ相対余錐を閉前置形状上の全図式へ戻す。
方針：持ち上げた全順序余錐同型の逆で前合成する。
規約：固定対象上の全 slice 図式を使用する。
使われ方：次の閉前置段の全交互図式。 -/
def extendedAlternatingDiagram {a : AlternatingIndex κ}
    {s : RelativeAlternatingOpenStage κ x I P a} {c : Fin 2}
    (t : RelativeAlternatingFactorization s c) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve {b : AlternatingIndex κ // b ≤ a}) ⟶
      sliceOver x :=
  (liftedCoconeIso.{u, u + 1} (F1B.posetLowerJoinIso a)).inv ≫
    (relativeSliceCocone s.diagram t.comparison).val

/-- 概要：新しい全図式は元の厳密前置図式を保持する。
方針：全余錐同型の左境界と相対余錐の固定条件を計算する。
規約：全単体上の厳密な制限の等式。
使われ方：全過去段との整合。 -/
lemma extendedAlternatingDiagram_old {a : AlternatingIndex κ}
    {s : RelativeAlternatingOpenStage κ x I P a} {c : Fin 2}
    (t : RelativeAlternatingFactorization s c) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (strictPrefixToClosed a)) ≫
      extendedAlternatingDiagram t = s.diagram := by
  have h : (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (strictPrefixToClosed a)) =
      joinInl _ Δ[0] ≫ (liftedCoconeIso.{u, u + 1} (F1B.posetLowerJoinIso a)).hom := by
    simp only [liftedCoconeIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← Category.assoc, uliftCoconeShapeIso_inv_inl, ← Functor.map_comp,
      F1B.posetLowerJoinIso_inl]
    rfl
  rw [h, extendedAlternatingDiagram, Category.assoc, Iso.hom_inv_id_assoc]
  exact (relativeSliceCocone s.diagram t.comparison).property

/-- 概要：現在成分の新しい全図式は同じ表示の延長添字で与えられる。
方針：成分余錐の全形状比較と元の比較辺の slice 制限を合成する。
規約：表示添字を交換せず全増大図式を一致させる。
使われ方：次の閉前置段の現在成分条件。 -/
lemma extendedAlternatingDiagram_current (a : κ.ord.ToType) (c : Fin 2)
    {s : RelativeAlternatingOpenStage κ x I P (toLex (a, c))}
    (t : RelativeAlternatingFactorization s c) :
    (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (alternatingClosedSection κ (toLex (a, c)) c)) ≫
        extendedAlternatingDiagram t =
      (SSet.uliftFunctor.{u + 1, u}).map (extendedComponentIndex κ a c t.index) ≫ P c := by
  apply (cancel_epi (liftedCoconeIso.{u, u + 1} (componentConeIso κ a c)).hom).1
  have h := liftedCoconeIso_naturality.{u, u + 1}
    (componentConeIso κ a c) (F1B.posetLowerJoinIso (toLex (a, c)))
    (nerveMap (alternatingLowerSection κ (toLex (a, c)) c))
    (nerveMap (alternatingClosedSection κ (toLex (a, c)) c))
    (alternatingConeShape_component κ a c)
  rw [← Category.assoc, ← h, extendedAlternatingDiagram, Category.assoc,
    Iso.hom_inv_id_assoc, t.component_slice]
  simp only [liftedCoconeIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    extendedComponentIndex, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map (componentConeIso κ a c).hom),
    ← Functor.map_comp, Iso.hom_inv_id, (SSet.uliftFunctor.{u + 1, u}).map_id, Category.id_comp]
  rw [uliftSliceUnderIso_hom_val, Category.assoc]

/-- 概要：現在以外の成分の新しい全図式は元の成分図式をそのまま保持する。
方針：他成分では閉前置包含が厳密前置包含を経由することを使う。
規約：元の表示添字を同じ値の部分型同型で戻す。
使われ方：次の閉前置段の他成分条件。 -/
lemma extendedAlternatingDiagram_other (a : κ.ord.ToType) (c d : Fin 2) (hd : d ≠ c)
    {s : RelativeAlternatingOpenStage κ x I P (toLex (a, c))}
    (t : RelativeAlternatingFactorization s c) :
    (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (alternatingClosedSection κ (toLex (a, c)) d)) ≫
        extendedAlternatingDiagram t =
      (SSet.uliftFunctor.{u + 1, u}).map
        ((otherComponentIso κ a c d hd).inv ≫ s.index d) ≫ P d := by
  apply (cancel_epi ((SSet.uliftFunctor.{u + 1, u}).map
    (otherComponentIso κ a c d hd).hom)).1
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (alternatingLowerSection κ (toLex (a, c)) d)) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map
          (nerveMap (strictPrefixToClosed (toLex (a, c)))) ≫
          extendedAlternatingDiagram t) := rfl
    _ = (SSet.uliftFunctor.{u + 1, u}).map (s.index d) ≫ P d := by
      rw [extendedAlternatingDiagram_old, s.component_eq]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map
        (otherComponentIso κ a c d hd).hom), ← Functor.map_comp,
        Iso.hom_inv_id, (SSet.uliftFunctor.{u + 1, u}).map_id, Category.id_comp]

/-- 概要：相対因子化から元の厳密前置段を保つ閉前置段が存在する。
方針：現在成分の余錐延長と他成分の同型輸送を全交互図式に接続する。
規約：因子化の存在を新しい仮定として追加せず、渡された具体的データを使う。
使われ方：実際の因子化存在定理を well-founded 再帰の延長条件に変換する。 -/
lemma exists_closedStage_of_relativeFactorization (a : κ.ord.ToType) (c : Fin 2)
    {s : RelativeAlternatingOpenStage κ x I P (toLex (a, c))}
    (t : RelativeAlternatingFactorization s c) :
    ∃ r : RelativeAlternatingClosedStage κ x I P (toLex (a, c)), r.ExtendsOpen s := by
  classical
  let J : ∀ d, nerve (AlternatingComponentClosed κ (toLex (a, c)) d) ⟶ I d := by
    intro d
    by_cases hd : d = c
    · subst d
      exact extendedComponentIndex κ a c t.index
    · exact (otherComponentIso κ a c d hd).inv ≫ s.index d
  have hJ : ∀ d, (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingClosedSection κ (toLex (a, c)) d)) ≫
      extendedAlternatingDiagram t = (SSet.uliftFunctor.{u + 1, u}).map (J d) ≫ P d := by
    intro d
    by_cases hd : d = c
    · subst d
      simpa only [J, dite_true] using extendedAlternatingDiagram_current a c t
    · simpa only [J, dite_eq_right hd] using extendedAlternatingDiagram_other a c d hd t
  refine ⟨⟨J, extendedAlternatingDiagram t, hJ⟩, extendedAlternatingDiagram_old t, ?_⟩
  intro d
  by_cases hd : d = c
  · subst d
    simpa only [J, dite_true] using extendedComponentIndex_old κ a c t.index
  · change nerveMap (alternatingComponentLowerToClosed κ (toLex (a, c)) d) ≫ J d = _
    simp only [J, dite_eq_right hd]
    rw [← otherComponentIso_hom κ a c d hd, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
