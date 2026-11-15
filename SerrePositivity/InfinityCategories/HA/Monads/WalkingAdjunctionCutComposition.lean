module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutInclusions

/-!
概要：隣り合う二つの切れ目の区間を水平合成すると全区間に戻る。
方針：重みの加法則と、先頭・残りの実包含の正方形で全射を照合する。
規約：任意の比較された三つの切れ目を使い、実分解の存在を仮定しない。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実因子の合成則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y M N P : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：実区間関手の射を包含の座標で評価する。
方針：全射の正方形を一点で評価する。規約：任意の比較された切れ目。
使われ方：Riehl–Verity §4.1の水平合成の照合。 -/
lemma walkingAdjunctionCutFunctor_square_val
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j)
    (k : Fin (walkingAdjunctionOrdinalCard M N
      ((walkingAdjunctionCutIntervalFunctor a b h).obj i))) :
    walkingAdjunctionCutCoordinate a j +
        (walkingAdjunctionOrderHom ((walkingAdjunctionCutIntervalFunctor a b h).map f) k).val =
      (walkingAdjunctionOrderHom (H.map f)
        (walkingAdjunctionCutFunctorInclusion a b h i k)).val := by
  exact congrArg Fin.val (congrArg (fun q => q k) (walkingAdjunctionCutFunctor_square a b h f))

/-- 概要：隣り合う実区間の対象の水平合成は全区間の対象。
方針：重みの加法則と比較された座標の差を使う。規約：全頂点。
使われ方：Riehl–Verity §4.1の水平合成の対象の照合。 -/
lemma walkingAdjunctionCutIntervalObject_comp
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (c : WalkingAdjunctionCut H P)
    (hab : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (hbc : ∀ i, walkingAdjunctionCutRank b i ≤ walkingAdjunctionCutRank c i)
    (i : Fin (n + 1)) :
    (walkingAdjunctionHorizontal M N P).obj
      (walkingAdjunctionCutIntervalObject a b hab i,
        walkingAdjunctionCutIntervalObject b c hbc i) =
      walkingAdjunctionCutIntervalObject a c (fun j => (hab j).trans (hbc j)) i := by
  apply walkingAdjunctionWeight_injective M P
  rw [walkingAdjunctionHorizontal_weight, walkingAdjunctionCutIntervalObject_weight,
    walkingAdjunctionCutIntervalObject_weight, walkingAdjunctionCutIntervalObject_weight]
  have hab' := walkingAdjunctionCutCoordinate_le a b i (hab i)
  have hbc' := walkingAdjunctionCutCoordinate_le b c i (hbc i)
  omega

/-- 概要：隣り合う実区間関手の水平合成は全区間関手。
方針：各点を先頭と残りに分け、実包含の正方形と同じ元の射で照合する。
規約：全関手の等式であり全射を含む。使われ方：Riehl–Verity §4.1–§4.2。 -/
lemma walkingAdjunctionCutIntervalFunctor_comp
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (c : WalkingAdjunctionCut H P)
    (hab : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (hbc : ∀ i, walkingAdjunctionCutRank b i ≤ walkingAdjunctionCutRank c i) :
    (walkingAdjunctionCutIntervalFunctor a b hab).prod'
        (walkingAdjunctionCutIntervalFunctor b c hbc) ⋙ walkingAdjunctionHorizontal M N P =
      walkingAdjunctionCutIntervalFunctor a c (fun i => (hab i).trans (hbc i)) := by
  let L := walkingAdjunctionCutIntervalFunctor a b hab
  let T := walkingAdjunctionCutIntervalFunctor b c hbc
  let R := walkingAdjunctionCutIntervalFunctor a c (fun i => (hab i).trans (hbc i))
  have ho (i : Fin (n + 1)) :
      (walkingAdjunctionHorizontal M N P).obj (L.obj i, T.obj i) = R.obj i :=
    walkingAdjunctionCutIntervalObject_comp a b c hab hbc i
  refine CategoryTheory.Functor.hext ho ?_
  intro i j f
  apply walkingAdjunctionOrderHom_hext (ho i) (ho j)
  apply ordinalHom_hext (congrArg (walkingAdjunctionOrdinalCard M P) (ho i))
    (congrArg (walkingAdjunctionOrdinalCard M P) (ho j))
  intro k l hkl
  change (walkingAdjunctionOrderHom ((walkingAdjunctionHorizontal M N P).map
      (X := (L.obj i, T.obj i)) (Y := (L.obj j, T.obj j)) (L.map f, T.map f)) k).val =
    (walkingAdjunctionOrderHom (R.map f) l).val
  have hR := walkingAdjunctionCutFunctor_square_val a c
    (fun i => (hab i).trans (hbc i)) f l
  change walkingAdjunctionCutCoordinate a j +
    (walkingAdjunctionOrderHom (R.map f) l).val = _ at hR
  have habi := walkingAdjunctionCutCoordinate_le a b i (hab i)
  have habj := walkingAdjunctionCutCoordinate_le a b j (hab j)
  by_cases hk : k.val < walkingAdjunctionOrdinalCard M N (L.obj i)
  · let z : Fin (walkingAdjunctionOrdinalCard M N (L.obj i)) := ⟨k.val, hk⟩
    have hzk : Fin.castLE (walkingAdjunctionHorizontal_prefix_card_le M N P
        (L.obj i) (T.obj i)) z = k := Fin.ext rfl
    have hc := walkingAdjunctionHorizontal_prefix_val M N P (L.map f) (T.map f) z
    rw [hzk] at hc
    have hL := walkingAdjunctionCutFunctor_square_val a b hab f z
    change walkingAdjunctionCutCoordinate a j +
      (walkingAdjunctionOrderHom (L.map f) z).val = _ at hL
    have he : walkingAdjunctionCutFunctorInclusion a b hab i z =
        walkingAdjunctionCutFunctorInclusion a c (fun i => (hab i).trans (hbc i)) i l := by
      apply Fin.ext
      simp only [walkingAdjunctionCutFunctorInclusion_val]
      exact congrArg (fun v : ℕ => walkingAdjunctionCutCoordinate a i + v) hkl
    rw [he] at hL
    exact hc.trans (by omega)
  · cases N
    · let z : Fin (walkingAdjunctionOrdinalCard .plus P (T.obj i)) :=
        ⟨k.val - walkingAdjunctionOrdinalCard M .plus (L.obj i), by
          have hs := walkingAdjunctionOrdinalCard_comp_plus M P (L.obj i) (T.obj i)
          have hb := k.isLt
          change k.val < walkingAdjunctionOrdinalCard M P
            ((walkingAdjunctionHorizontal M .plus P).obj (L.obj i, T.obj i)) at hb
          omega⟩
      have hc := ordinalOrderHom_heq_val
        (walkingAdjunctionOrdinalCard_comp_plus M P (L.obj i) (T.obj i))
        (walkingAdjunctionOrdinalCard_comp_plus M P (L.obj j) (T.obj j))
        _ _ (walkingAdjunctionOrderHom_comp_plus M P (L.map f) (T.map f))
        k (z.natAdd (walkingAdjunctionOrdinalCard M .plus (L.obj i))) (by
          change k.val = walkingAdjunctionOrdinalCard M .plus (L.obj i) +
            (k.val - walkingAdjunctionOrdinalCard M .plus (L.obj i))
          omega)
      rw [ordinalAppend_natAdd] at hc
      have hLi := walkingAdjunctionCutIntervalObject_card a b hab i
      have hLj := walkingAdjunctionCutIntervalObject_card a b hab j
      change walkingAdjunctionOrdinalCard M .plus (L.obj i) =
        walkingAdjunctionCutCoordinate b i - walkingAdjunctionCutCoordinate a i + 0 at hLi
      change walkingAdjunctionOrdinalCard M .plus (L.obj j) =
        walkingAdjunctionCutCoordinate b j - walkingAdjunctionCutCoordinate a j + 0 at hLj
      have hT := walkingAdjunctionCutFunctor_square_val b c hbc f z
      change walkingAdjunctionCutCoordinate b j +
        (walkingAdjunctionOrderHom (T.map f) z).val = _ at hT
      have he : walkingAdjunctionCutFunctorInclusion b c hbc i z =
          walkingAdjunctionCutFunctorInclusion a c (fun i => (hab i).trans (hbc i)) i l := by
        apply Fin.ext
        change walkingAdjunctionCutCoordinate b i +
            (k.val - walkingAdjunctionOrdinalCard M .plus (L.obj i)) =
          walkingAdjunctionCutCoordinate a i + l.val
        omega
      rw [he] at hT
      change _ = walkingAdjunctionOrdinalCard M .plus (L.obj j) +
        (walkingAdjunctionOrderHom (T.map f) z).val at hc
      omega
    · let z : Fin (walkingAdjunctionOrdinalCard .minus P (T.obj i)) :=
        ⟨k.val - walkingAdjunctionIncomingDim M (L.obj i), by
          have hs := walkingAdjunctionOrdinalCard_comp_minus M P (L.obj i) (T.obj i)
          have ht := walkingAdjunctionOutgoing_card P (T.obj i)
          have hb := k.isLt
          change k.val < walkingAdjunctionOrdinalCard M P
            ((walkingAdjunctionHorizontal M .minus P).obj (L.obj i, T.obj i)) at hb
          omega⟩
      have hc := ordinalOrderHom_heq_val
        (walkingAdjunctionOrdinalCard_comp_minus M P (L.obj i) (T.obj i))
        (walkingAdjunctionOrdinalCard_comp_minus M P (L.obj j) (T.obj j))
        _ _ (walkingAdjunctionOrderHom_comp_minus M P (L.map f) (T.map f))
        k (⟨k.val, by
          have hs := walkingAdjunctionOrdinalCard_comp_minus M P (L.obj i) (T.obj i)
          have hb := k.isLt
          change k.val < walkingAdjunctionOrdinalCard M P
            ((walkingAdjunctionHorizontal M .minus P).obj (L.obj i, T.obj i)) at hb
          omega⟩) rfl
      have hgap : walkingAdjunctionIncomingDim M (L.obj i) < k.val := by
        have hl := walkingAdjunctionIncoming_card M (L.obj i)
        omega
      rw [ordinalGlue_val_of_lt _ _ _ hgap] at hc
      have hz : k.val - walkingAdjunctionIncomingDim M (L.obj i) <
          walkingAdjunctionOutgoingDim P (T.obj i) + 1 := by
        have ht := walkingAdjunctionOutgoing_card P (T.obj i)
        have hb := z.isLt
        change k.val - walkingAdjunctionIncomingDim M (L.obj i) <
          walkingAdjunctionOrdinalCard .minus P (T.obj i) at hb
        omega
      have ht := ordinalOrderHom_heq_val (walkingAdjunctionOutgoing_card P (T.obj i)).symm
        (walkingAdjunctionOutgoing_card P (T.obj j)).symm
        _ _ (walkingAdjunctionOutgoingMap_heq (T.map f)) ⟨_, hz⟩ z rfl
      have hc' := hc.trans (congrArg
        (fun v : ℕ => walkingAdjunctionIncomingDim M (L.obj j) + v) ht)
      have hDi := walkingAdjunctionIncomingDim_weight M (L.obj i)
      have hDj := walkingAdjunctionIncomingDim_weight M (L.obj j)
      have hWi := walkingAdjunctionCutIntervalObject_weight a b hab i
      have hWj := walkingAdjunctionCutIntervalObject_weight a b hab j
      change walkingAdjunctionWeight M .minus (L.obj i) =
        walkingAdjunctionCutCoordinate b i - walkingAdjunctionCutCoordinate a i at hWi
      change walkingAdjunctionWeight M .minus (L.obj j) =
        walkingAdjunctionCutCoordinate b j - walkingAdjunctionCutCoordinate a j at hWj
      have hT := walkingAdjunctionCutFunctor_square_val b c hbc f z
      change walkingAdjunctionCutCoordinate b j +
        (walkingAdjunctionOrderHom (T.map f) z).val = _ at hT
      have he : walkingAdjunctionCutFunctorInclusion b c hbc i z =
          walkingAdjunctionCutFunctorInclusion a c (fun i => (hab i).trans (hbc i)) i l := by
        apply Fin.ext
        change walkingAdjunctionCutCoordinate b i +
            (k.val - walkingAdjunctionIncomingDim M (L.obj i)) =
          walkingAdjunctionCutCoordinate a i + l.val
        omega
      rw [he] at hT
      omega

end SerrePositivity.InfinityCategories.HA.Monads
