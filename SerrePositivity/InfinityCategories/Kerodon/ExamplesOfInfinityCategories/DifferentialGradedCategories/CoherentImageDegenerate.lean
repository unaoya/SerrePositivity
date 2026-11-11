module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathImageFlag

/-!
# 潰れた内部座標を持つ coherent 成分の消滅

概要：内部座標が端点か他の内部座標と同じ像を持てば、引き戻した coherent 成分は零となる。
方針：各最大旗で重複する座標のうち後から加わるものを選び、隣接頂点の反復を使う。
規約：二つの内部座標を同一視する場合も、射影による座標忘却は仮定しない。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の非単射な引き戻しの高次成分。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
variable {J K : Type u} [LinearOrder J] [LinearOrder K] {a b : J}

/-- 概要：像で隣接頂点が繰り返す Path の旗は coherent Hom で零と評価される。
方針：native な豊穣写像を薄い圏の nerve の退化評価の補題に適用する。
規約：像の両端が等しくてもよい。
使われ方：Kerodon 2.5.9（Tag 00SC） の各置換の旗の消去。 -/
lemma cubeFlagEvaluation_coherentImage_zero
    (s : EnrichedFunctor SSet (SimplicialThickening K) (ClosedCategory R D))
    (f : J →o K) (hab : a < b) (S : Finset (Set.Ioo a b))
    {n : ℕ} (e : Fin n ≃ S) (i : Fin n)
    (hi : f (e i).val.val = f a ∨ f (e i).val.val = f b ∨
      ∃ j : Fin n, j.val < i.val ∧ f (e j).val.val = f (e i).val.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom ((SimplicialThickening.functor f).comp SSet s) hab S) = 0 := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) (D := D) (s.obj (.mk (f a))) (s.obj (.mk (f b))) n
    ((s.map (.mk (f a)) (.mk (f b))).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathImageFlag f hab S e)) = 0
  have : Quiver.IsThin (SimplicialThickening.Path (f a) (f b)) := by
    intro p q
    exact ⟨fun g h ↦ InducedCategory.hom_ext (Subsingleton.elim g.hom h.hom)⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval_thin_nerve_repeat_zero _ _ i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathImageFlag_repeat f hab S e i hi)

/-- 概要：内部座標の像が端点の像なら、その coherent 立方体評価は零である。
方針：各置換でその座標が加わる時点の頂点反復を使う。
規約：座標が一つだけの場合も含む。
使われ方：HA 1.3.1.16 の端点へ潰れる退化の高次成分。 -/
lemma cubeEvaluation_coherentImage_zero_of_endpoint
    (s : EnrichedFunctor SSet (SimplicialThickening K) (ClosedCategory R D))
    (f : J →o K) (hab : a < b) (S : Finset (Set.Ioo a b))
    {n : ℕ} (e : Fin n ≃ S) (t : S) (ht : f t.val.val = f a ∨ f t.val.val = f b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom ((SimplicialThickening.functor f).comp SSet s) hab S) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation
  apply Finset.sum_eq_zero
  intro σ _
  have ht' : f ((σ.trans e) ((σ.trans e).symm t)).val.val = f a ∨
      f ((σ.trans e) ((σ.trans e).symm t)).val.val = f b := by simpa using ht
  rw [cubeFlagEvaluation_coherentImage_zero s f hab S (σ.trans e)
    ((σ.trans e).symm t) (ht'.imp_right Or.inl), smul_zero]

/-- 概要：異なる内部座標が同じ像を持てば、その coherent 立方体評価は零である。
方針：各置換で二つの座標の後のものを取り、その像が既に旗に現れることを使う。
規約：像への写像の全体での単射性は要求しない。
使われ方：Kerodon 2.5.9（Tag 00SC） の内部点が重複する退化の高次成分。 -/
lemma cubeEvaluation_coherentImage_zero_of_collision
    (s : EnrichedFunctor SSet (SimplicialThickening K) (ClosedCategory R D))
    (f : J →o K) (hab : a < b) (S : Finset (Set.Ioo a b))
    {n : ℕ} (e : Fin n ≃ S) (t w : S) (htw : t ≠ w) (he : f t.val.val = f w.val.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom ((SimplicialThickening.functor f).comp SSet s) hab S) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation
  apply Finset.sum_eq_zero
  intro σ _
  let q := σ.trans e
  have hne : q.symm t ≠ q.symm w := fun h ↦ htw (q.symm.injective h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h : ∃ j : Fin n, j.val < (q.symm w).val ∧
        f (q j).val.val = f (q (q.symm w)).val.val :=
      ⟨q.symm t, hlt, by simpa using he⟩
    rw [cubeFlagEvaluation_coherentImage_zero s f hab S q (q.symm w)
      (Or.inr (Or.inr h)), smul_zero]
  · have h : ∃ j : Fin n, j.val < (q.symm t).val ∧
        f (q j).val.val = f (q (q.symm t)).val.val :=
      ⟨q.symm w, hgt, by simpa using he.symm⟩
    rw [cubeFlagEvaluation_coherentImage_zero s f hab S q (q.symm t)
      (Or.inr (Or.inr h)), smul_zero]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
