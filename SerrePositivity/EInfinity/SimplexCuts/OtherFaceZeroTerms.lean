module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedFaceTensors

/-!
# 削除しない色の退化による境界項の消滅

Berger–Fresse §2.2.6–7、M14 L09a。
既存の各色の面の単射性と、正規化生成元・実テンソルの消滅を接続する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C202：同色の二頂点で垂直座標が一致すると、その色の元の面は非単射。 -/
lemma face_not_mono_of_repeated_color {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) (i j : Fin (m + q + 1))
    (hi : label s v.val i = c) (hj : label s v.val j = c)
    (hne : i ≠ j) (hv : s.vertical i = s.vertical j) : ¬Mono (face s v c) := by
  intro hm
  have hci : i ∈ colorPositions s v.val c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hcj : j ∈ colorPositions s v.val c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  let e := (colorPositions s v.val c).orderIsoOfFin (colorPositions_card_eq s v c)
  let ii := e.symm ⟨i, hci⟩
  let jj := e.symm ⟨j, hcj⟩
  have hei : (colorPositions s v.val c).orderEmbOfFin (colorPositions_card_eq s v c) ii = i :=
    congrArg Subtype.val (e.apply_symm_apply ⟨i, hci⟩)
  have hej : (colorPositions s v.val c).orderEmbOfFin (colorPositions_card_eq s v c) jj = j :=
    congrArg Subtype.val (e.apply_symm_apply ⟨j, hcj⟩)
  have hval : vertices s v c ii = vertices s v c jj := by
    change s.vertical _ = s.vertical _
    rw [hei, hej]
    exact hv
  have heq : ii = jj := (SimplexCategory.mono_iff_injective.mp hm) hval
  exact hne (hei.symm.trans ((congrArg
    ((colorPositions s v.val c).orderEmbOfFin (colorPositions_card_eq s v c)) heq).trans hej))

/-- C203：削除しない色の元の面が非単射なら、指定削除の実テンソルは零。 -/
lemma deletedCutTensor_eq_zero_of_other_face {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (ha : 0 < outputDegree s v a)
    (j : Fin (outputDegree s v a + 1)) (c : Fin r) (hc : c ≠ a)
    (hm : ¬Mono (face s v c)) (x : S _⦋q⦌) :
    deletedCutTensor A S s v a ha j x = 0 := by
  unfold deletedCutTensor
  dsimp only
  rw [tensorValue_eq_zero _ _ _ _ c ?_, map_zero]
  simp only [dite_eq_right hc, gen_map_of_not_mono A S _ _ hm x, map_zero]

/-- C204：同じ退化の消滅は、元の符号付き境界項にも成り立つ。 -/
lemma outputBoundaryTerm_eq_zero_of_other_face {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s v a + 1))
    (c : Fin r) (hc : c ≠ a) (hm : ¬Mono (face s v c)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v a j x = 0 := by
  unfold outputBoundaryTerm
  split_ifs with ha
  · rw [deletedCutTensor_eq_zero_of_other_face A S s v a ha j c hc hm x, smul_zero]
  · rfl

end SerrePositivity.EInfinity.SimplexCuts
