module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiData
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents

/-!
概要：bar の Bianchi データの先頭面を、元の coherent 単体へ厳密に戻す。
方針：末端の置換が先頭面を保つことと、末端退化の先頭制限が恒等であることを使う。
規約：元の全斉次成分を保持し、方程式の仮定を追加しない。
使われ方：末端への HA 右辺に現れる左切断と元の prefix の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarBianchiData_front {n : ℕ} (σ : I _⦋n⦌) :
    (dgCoherentBarBianchiData R D F σ).pullback Fin.castSuccOrderEmb.toOrderHom =
      (coherentDiagramSimplex F σ).toSimplexData := by
  unfold dgCoherentBarBianchiData
  rw [SimplexData.lastReplacement_front]
  change ((coherentDiagramSimplex F σ).toSimplexData.pullback
    (Fin.last n).predAboveOrderHom).pullback Fin.castSuccOrderEmb.toOrderHom = _
  rw [SimplexData.pullback_comp]
  have hid : (Fin.last n).predAboveOrderHom.comp Fin.castSuccOrderEmb.toOrderHom =
      OrderHom.id := by
    apply DFunLike.ext
    intro j
    exact Fin.predAbove_last_castSucc
  rw [hid, SimplexData.pullback_id]

lemma dgCoherentBarBianchiData_obj_castSucc {n : ℕ} (σ : I _⦋n⦌) (i : Fin (n + 1)) :
    (dgCoherentBarBianchiData R D F σ).obj i.castSucc =
      (coherentDiagramSimplex F σ).obj i :=
  congrArg (fun s : SimplexData R (RightModule R D) n => s.obj i)
    (dgCoherentBarBianchiData_front R D F σ)

lemma dgCoherentBarBianchiData_obj_last {n : ℕ} (σ : I _⦋n⦌) :
    (dgCoherentBarBianchiData R D F σ).obj (Fin.last (n + 1)) =
      ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F) :=
  SimplexData.lastReplacementObj_last _ _

lemma dgCoherentBarBianchiData_hom_front {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq ((dgCoherentBarBianchiData R D F σ).hom (J.image Fin.castSucc)
      a.castSucc b.castSucc k (Index.image_two (Fin.castSucc_injective _).injOn hJ)
      (Index.image_min Fin.castSuccOrderEmb.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max Fin.castSuccOrderEmb.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]; exact hk))
      ((coherentDiagramSimplex F σ).hom J a b k hJ ha hb hk) := by
  have hh := SimplexData.hom_heq_of_eq (dgCoherentBarBianchiData_front R D F σ)
    J a b k hJ ha hb hk
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    (Fin.castSucc_injective _).injOn] at hh
  exact hh

end SerrePositivity.InfinityCategories
