module

public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentNoninjectiveNaturality

/-!
# 潰れた二点集合の比較成分

概要：二点の像が一致する場合、coherent 比較成分は dg 単位となる。
方針：像の Path がループの恒等射であることと、豊穣関手の単位保存を使う。
規約：端点と次数の表示の差を HEq で吸収する。
使われ方：HA 1.3.1.16、Kerodon 2.5.9 の比較写像の退化辺の分岐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：端点が一致する Path の零単体は豊穣関手によって dg 単位と評価される。
方針：唯一のループを豊穣単位の零単体に同定し、単位保存を評価する。
規約：二端点の同一視は明示的な等式として受け取る。
使われ方：Kerodon 2.5.9 の潰れた辺の評価。 -/
lemma standardTopEval_collapsed_path {K : Type u} [LinearOrder K]
    (s : EnrichedFunctor SSet (SimplicialThickening K) (ClosedCategory R D))
    {c d : K} (h : c = d) (p : (nerve (Path c d)) _⦋0⦌) :
    HEq (standardTopEval (R := R) (D := D) (s.obj (.mk c)) (s.obj (.mk d)) 0
      ((s.map (.mk c) (.mk d)).app _ p)) (unitElement R (s.obj (.mk d))).val := by
  subst d
  have hp : p = (eId SSet (SimplicialThickening.mk c)).app _ PUnit.unit :=
    CategoryTheory.Functor.ext (fun t ↦ Coherent.pathLoop_eq_id c (p.obj t))
  have hs : (s.map (.mk c) (.mk c)).app (Opposite.op ⦋0⦌)
      ((eId SSet (SimplicialThickening.mk c)).app (Opposite.op ⦋0⦌) PUnit.unit) =
        standardUnit (R := R) (D := D) (s.obj (.mk c)) 0 := by
    exact congrArg (fun φ : MonoidalCategory.tensorUnit SSet ⟶
      standardHomSpace (R := R) (D := D) (s.obj (.mk c)) (s.obj (.mk c)) ↦
        φ.app (Opposite.op ⦋0⦌) PUnit.unit) (s.map_id (.mk c))
  rw [hp, hs]
  exact heq_of_eq (congrArg Subtype.val (standardZeroEval_unit (R := R) (D := D)
    (s.obj (.mk c))))

/-- 概要：内部点のない立方体で両端の像が等しければ比較成分は dg 単位である。
方針：零次立方体の唯一の旗を像のループの零単体として評価する。
規約：元の二端点は異なり、像で一致する。
使われ方：HA 1.3.1.16 の二点集合が潰れる場合の成分。 -/
lemma coherentCubeComponent_image_empty_heq_unit
    {J K : Type u} [LinearOrder J] [LinearOrder K] {a b : J}
    (s : EnrichedFunctor SSet (SimplicialThickening K) (ClosedCategory R D))
    (f : J →o K) (hab : a < b) (h : f a = f b) :
    HEq (coherentCubeComponent ((SimplicialThickening.functor f).comp SSet s)
      hab ∅) (unitElement R (s.obj (.mk (f b)))).val := by
  change HEq (cubeEvaluation (R := R) (D := D)
    (descendingEnumeration (∅ : Finset (Set.Ioo a b)))
      (coherentCubeHom ((SimplicialThickening.functor f).comp SSet s) hab ∅)) _
  rw [cubeEvaluation_zero]
  exact standardTopEval_collapsed_path s h
    (pathImageFlag f hab ∅ (descendingEnumeration ∅))

/-- 概要：潰れた二点集合の比較成分族の hom は既存の dg 引き戻しの hom と等しい。
方針：内部点集合が空であることから、両側を dg 単位に異種等号で同定する。
規約：非単射な二点集合に余分な整合性の仮定はない。
使われ方：Kerodon 2.5.9 の比較写像の単体的自然性の最後の分岐。 -/
lemma coherentSimplexData_pullback_hom_of_collapsed_pair {m n : ℕ}
    (s : (doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (DGNerve.Index.nonempty hI))
    (hb : b = I.max' (DGNerve.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hi : ¬ Set.InjOn α (I : Set _)) (hc : I.card = 2) :
    (coherentSimplexData ((SimplicialThickening.functor α.uliftMap).comp SSet s)).hom
      I a b k hI ha hb hk =
        ((coherentSimplexData s).pullback α).hom I a b k hI ha hb hk := by
  have ha₀ : IsLeast (I : Set _) a := by rw [ha]; exact I.isLeast_min' _
  have hb₀ : IsGreatest (I : Set _) b := by rw [hb]; exact I.isGreatest_max' _
  have hab : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
  have he : α a = α b := DGNerve.Index.collapse_two hi hc ha₀ hb₀
  have hS : coherentVertexInterior.{u} I a b = ∅ := by
    apply Finset.card_eq_zero.mp
    have h := coherentVertexInterior_card.{u} ha₀ hb₀ hab
    omega
  apply eq_of_heq
  apply (coherentSimplexData_hom_heq _ I a b k hI ha hb hk).trans
  apply (coherentCubeComponent_heq_of_set_eq _ _ _ _ hS).trans
  apply (coherentCubeComponent_image_empty_heq_unit s α.uliftMap
    (show (ULift.up a : ULift.{u} (Fin (m + 1))) < ULift.up b from hab)
    (congrArg ULift.up he)).trans
  exact (DGNerve.SimplexData.pullback_hom_of_collapsed_pair
    (coherentSimplexData s) α I a b k hI ha hb hk hi hc).symm

end SerrePositivity.InfinityCategories.DoldKanComparison
