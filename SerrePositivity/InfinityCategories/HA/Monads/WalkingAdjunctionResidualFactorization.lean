module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionResidualInclusions

/-!
概要：残りの実関手と元の因子の水平合成が、元の分解へ全関手として戻ることを証明する。
方針：左は先頭と残りの区間の全点、右は全結合則と全合成の忠実性を使う。
規約：対象の等式だけで終えない。使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な語の一意性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：短い左因子と残りの実関手の水平合成は、長い左因子に全関手として一致する。
方針：先頭と残りの包含の正方形を全点で使う。
規約：全射を同じ共通表示で照合する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.residual_prefix (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) :
    a.left.prod' (a.residualFunctor b h) ⋙ walkingAdjunctionHorizontal X a.middle b.middle =
      b.left := by
  rcases a with ⟨M, L, R, ha⟩
  let a : WalkingAdjunctionFactorization H := ⟨M, L, R, ha⟩
  let T := a.residualFunctor b h
  change L.prod' T ⋙ walkingAdjunctionHorizontal X M b.middle = b.left
  have ho (i : Fin (n + 1)) :
      (walkingAdjunctionHorizontal X M b.middle).obj (L.obj i, T.obj i) = b.left.obj i :=
    walkingAdjunctionResidualObject_prefix (L.obj i) (b.left.obj i) (h i)
  refine CategoryTheory.Functor.hext ho ?_
  intro i j f
  apply walkingAdjunctionOrderHom_hext (ho i) (ho j)
  apply ordinalHom_hext (congrArg (walkingAdjunctionOrdinalCard X b.middle) (ho i))
    (congrArg (walkingAdjunctionOrdinalCard X b.middle) (ho j))
  intro k l hkl
  have hB := congrArg Fin.val (congrArg
    (fun q : Fin (walkingAdjunctionOrdinalCard X b.middle (b.left.obj i)) →o
      Fin (walkingAdjunctionOrdinalCard X Y (H.obj j)) => q l) (b.prefix_square f))
  change (walkingAdjunctionOrderHom (b.left.map f) l).val =
    (walkingAdjunctionOrderHom (H.map f) (b.prefixInclusion i l)).val at hB
  by_cases hk : k.val < walkingAdjunctionOrdinalCard X M (L.obj i)
  · let z : Fin (walkingAdjunctionOrdinalCard X M (L.obj i)) := ⟨k.val, hk⟩
    have hzk : Fin.castLE
        (walkingAdjunctionHorizontal_prefix_card_le X M b.middle (L.obj i) (T.obj i)) z = k :=
      Fin.ext rfl
    have hc := walkingAdjunctionHorizontal_prefix_val X M b.middle (L.map f) (T.map f) z
    rw [hzk] at hc
    have hA := congrArg Fin.val (congrArg
      (fun q : Fin (walkingAdjunctionOrdinalCard X M (L.obj i)) →o
        Fin (walkingAdjunctionOrdinalCard X Y (H.obj j)) => q z) (a.prefix_square f))
    change (walkingAdjunctionOrderHom (L.map f) z).val =
      (walkingAdjunctionOrderHom (H.map f) (a.prefixInclusion i z)).val at hA
    have he : a.prefixInclusion i z = b.prefixInclusion i l := Fin.ext hkl
    exact hc.trans (hA.trans ((congrArg
      (fun p => (walkingAdjunctionOrderHom (H.map f) p).val) he).trans hB.symm))
  · cases M
    · let z : Fin (walkingAdjunctionOrdinalCard .plus b.middle (T.obj i)) :=
        ⟨k.val - walkingAdjunctionOrdinalCard X .plus (L.obj i), by
          have hs := walkingAdjunctionOrdinalCard_comp_plus X b.middle (L.obj i) (T.obj i)
          have hb := k.isLt
          change k.val < walkingAdjunctionOrdinalCard X b.middle
            ((walkingAdjunctionHorizontal X .plus b.middle).obj (L.obj i, T.obj i)) at hb
          omega⟩
      have hc := ordinalOrderHom_heq_val
        (walkingAdjunctionOrdinalCard_comp_plus X b.middle (L.obj i) (T.obj i))
        (walkingAdjunctionOrdinalCard_comp_plus X b.middle (L.obj j) (T.obj j))
        _ _ (walkingAdjunctionOrderHom_comp_plus X b.middle (L.map f) (T.map f))
        k (z.natAdd (walkingAdjunctionOrdinalCard X .plus (L.obj i))) (by
          change k.val = walkingAdjunctionOrdinalCard X .plus (L.obj i) +
            (k.val - walkingAdjunctionOrdinalCard X .plus (L.obj i))
          omega)
      rw [ordinalAppend_natAdd] at hc
      have hr := congrArg Fin.val (congrArg
        (fun q : Fin (walkingAdjunctionOrdinalCard .plus b.middle (T.obj i)) →o
          Fin (walkingAdjunctionOrdinalCard X Y (H.obj j)) => q z) (a.residual_square b h f))
      change walkingAdjunctionCutCoordinate a.cut j +
          (walkingAdjunctionOrderHom (T.map f) z).val =
        (walkingAdjunctionOrderHom (H.map f) (a.residualInclusion b h i z)).val at hr
      have hAi := a.prefix_card i
      have hAj := a.prefix_card j
      change walkingAdjunctionOrdinalCard X .plus (L.obj i) =
        walkingAdjunctionCutCoordinate a.cut i + 0 at hAi
      change walkingAdjunctionOrdinalCard X .plus (L.obj j) =
        walkingAdjunctionCutCoordinate a.cut j + 0 at hAj
      have he : a.residualInclusion b h i z = b.prefixInclusion i l := by
        apply Fin.ext
        change walkingAdjunctionCutCoordinate a.cut i +
          (k.val - walkingAdjunctionOrdinalCard X .plus (L.obj i)) = l.val
        omega
      have hc' : (walkingAdjunctionOrderHom
          ((walkingAdjunctionHorizontal X .plus b.middle).map
            (X := (L.obj i, T.obj i)) (Y := (L.obj j, T.obj j)) (L.map f, T.map f)) k).val =
          walkingAdjunctionCutCoordinate a.cut j + (walkingAdjunctionOrderHom (T.map f) z).val := by
        have hcNat := hc
        change _ = walkingAdjunctionOrdinalCard X .plus (L.obj j) +
          (walkingAdjunctionOrderHom (T.map f) z).val at hcNat
        have hAj' : walkingAdjunctionOrdinalCard X .plus (L.obj j) =
            walkingAdjunctionCutCoordinate a.cut j := by
          simpa only [Nat.add_zero] using hAj
        exact hcNat.trans (congrArg
          (fun v : ℕ => v + (walkingAdjunctionOrderHom (T.map f) z).val) hAj')
      exact hc'.trans (hr.trans ((congrArg
        (fun p => (walkingAdjunctionOrderHom (H.map f) p).val) he).trans hB.symm))
    · let z : Fin (walkingAdjunctionOrdinalCard .minus b.middle (T.obj i)) :=
        ⟨k.val - walkingAdjunctionIncomingDim X (L.obj i), by
          have hs := walkingAdjunctionOrdinalCard_comp_minus X b.middle (L.obj i) (T.obj i)
          have ht := walkingAdjunctionOutgoing_card b.middle (T.obj i)
          have hb := k.isLt
          change k.val < walkingAdjunctionOrdinalCard X b.middle
            ((walkingAdjunctionHorizontal X .minus b.middle).obj (L.obj i, T.obj i)) at hb
          omega⟩
      have hc := ordinalOrderHom_heq_val
        (walkingAdjunctionOrdinalCard_comp_minus X b.middle (L.obj i) (T.obj i))
        (walkingAdjunctionOrdinalCard_comp_minus X b.middle (L.obj j) (T.obj j))
        _ _ (walkingAdjunctionOrderHom_comp_minus X b.middle (L.map f) (T.map f))
        k (⟨k.val, by
          have hs := walkingAdjunctionOrdinalCard_comp_minus X b.middle (L.obj i) (T.obj i)
          have hb := k.isLt
          change k.val < walkingAdjunctionOrdinalCard X b.middle
            ((walkingAdjunctionHorizontal X .minus b.middle).obj (L.obj i, T.obj i)) at hb
          omega⟩) rfl
      have hgap : walkingAdjunctionIncomingDim X (L.obj i) < k.val := by
        have hl := walkingAdjunctionIncoming_card X (L.obj i)
        omega
      rw [ordinalGlue_val_of_lt _ _ _ hgap] at hc
      have hz : k.val - walkingAdjunctionIncomingDim X (L.obj i) <
          walkingAdjunctionOutgoingDim b.middle (T.obj i) + 1 := by
        have ht := walkingAdjunctionOutgoing_card b.middle (T.obj i)
        have hb := z.isLt
        change k.val - walkingAdjunctionIncomingDim X (L.obj i) <
          walkingAdjunctionOrdinalCard .minus b.middle (T.obj i) at hb
        omega
      have ht := ordinalOrderHom_heq_val (walkingAdjunctionOutgoing_card b.middle (T.obj i)).symm
        (walkingAdjunctionOutgoing_card b.middle (T.obj j)).symm
        _ _ (walkingAdjunctionOutgoingMap_heq (T.map f)) ⟨_, hz⟩ z rfl
      have hc' := hc.trans (congrArg
        (fun v : ℕ => walkingAdjunctionIncomingDim X (L.obj j) + v) ht)
      have hDimi : walkingAdjunctionIncomingDim X (L.obj i) =
          walkingAdjunctionCutCoordinate a.cut i :=
        (walkingAdjunctionIncomingDim_weight X (L.obj i)).trans (a.cut_coordinate i).symm
      have hDimj : walkingAdjunctionIncomingDim X (L.obj j) =
          walkingAdjunctionCutCoordinate a.cut j :=
        (walkingAdjunctionIncomingDim_weight X (L.obj j)).trans (a.cut_coordinate j).symm
      have hr := congrArg Fin.val (congrArg
        (fun q : Fin (walkingAdjunctionOrdinalCard .minus b.middle (T.obj i)) →o
          Fin (walkingAdjunctionOrdinalCard X Y (H.obj j)) => q z) (a.residual_square b h f))
      change walkingAdjunctionCutCoordinate a.cut j +
          (walkingAdjunctionOrderHom (T.map f) z).val =
        (walkingAdjunctionOrderHom (H.map f) (a.residualInclusion b h i z)).val at hr
      have he : a.residualInclusion b h i z = b.prefixInclusion i l := by
        apply Fin.ext
        change walkingAdjunctionCutCoordinate a.cut i +
          (k.val - walkingAdjunctionIncomingDim X (L.obj i)) = l.val
        omega
      have hc'' := hc'.trans (congrArg
        (fun v : ℕ => v + (walkingAdjunctionOrderHom (T.map f) z).val) hDimj)
      exact hc''.trans (hr.trans ((congrArg
        (fun p => (walkingAdjunctionOrderHom (H.map f) p).val) he).trans hB.symm))

/-- 概要：残りの実関手と短い右因子の合成は、長い右因子に全関手として一致する。
方針：左の合成の照合と全結合則を使い、固定した左因子を忠実性で消す。
規約：対象と全射を回収する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.residual_suffix (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) :
    (a.residualFunctor b h).prod' b.right ⋙ walkingAdjunctionHorizontal a.middle b.middle Y =
      a.right := by
  let T := a.residualFunctor b h
  let C := T.prod' b.right ⋙ walkingAdjunctionHorizontal a.middle b.middle Y
  have hR (i : Fin (n + 1)) : a.right.obj i = C.obj i := by
    exact (walkingAdjunctionResidualObject_suffix
      (a.left.obj i) (b.left.obj i) (a.right.obj i) (b.right.obj i) (h i)
      (CategoryTheory.Functor.congr_obj (a.fac.trans b.fac.symm) i)).symm
  have hc : a.left.prod' a.right ⋙ walkingAdjunctionHorizontal X a.middle Y =
      a.left.prod' C ⋙ walkingAdjunctionHorizontal X a.middle Y := by
    calc
      _ = H := a.fac
      _ = b.left.prod' b.right ⋙ walkingAdjunctionHorizontal X b.middle Y := b.fac.symm
      _ = (a.left.prod' T ⋙ walkingAdjunctionHorizontal X a.middle b.middle).prod' b.right ⋙
          walkingAdjunctionHorizontal X b.middle Y := by rw [a.residual_prefix b h]
      _ = _ := walkingAdjunctionHorizontal_assoc X a.middle b.middle Y a.left T b.right
  obtain ⟨_, he⟩ := walkingAdjunctionHorizontal_functor_inj X a.middle Y
    a.left a.left a.right C (fun _ => rfl) hR hc
  exact he.symm

/-- 概要：同じ全単体の二つの実水平分解には、実関手による一方の細分が存在する。
方針：左因子の全比較と残りの実関手の二つの合成の等式を使う。
規約：細分の関手を存在の仮定にしない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma WalkingAdjunctionFactorization.exists_refinement (a b : WalkingAdjunctionFactorization H) :
    (∃ T : Fin (n + 1) ⥤ walkingAdjunctionHom a.middle b.middle,
      a.left.prod' T ⋙ walkingAdjunctionHorizontal X a.middle b.middle = b.left ∧
      T.prod' b.right ⋙ walkingAdjunctionHorizontal a.middle b.middle Y = a.right) ∨
    (∃ T : Fin (n + 1) ⥤ walkingAdjunctionHom b.middle a.middle,
      b.left.prod' T ⋙ walkingAdjunctionHorizontal X b.middle a.middle = a.left ∧
      T.prod' a.right ⋙ walkingAdjunctionHorizontal b.middle a.middle Y = b.right) := by
  rcases a.prefix_total b with h | h
  · exact Or.inl ⟨a.residualFunctor b h, a.residual_prefix b h, a.residual_suffix b h⟩
  · exact Or.inr ⟨b.residualFunctor a h, b.residual_prefix a h, b.residual_suffix a h⟩

end SerrePositivity.InfinityCategories.HA.Monads
