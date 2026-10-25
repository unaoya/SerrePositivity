module
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents

/-!
概要：面への制限が等しい二つのデータの、その面内の全 Hom 成分を比較する。
方針：面の逆像を有限集合として取り、既存の単射像の成分比較を元の添字へ戻す。
規約：対象と次数を保持した異種等号を使い、方程式は要求しない。
使われ方：末端を置換した bar データの、単射制限の先頭側の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

lemma hom_heq_of_face_pullback_eq {n : ℕ} (s t : SimplexData A D (n + 1))
    (j : Fin (n + 2))
    (h : s.pullback j.succAboveOrderEmb.toOrderHom = t.pullback j.succAboveOrderEmb.toOrderHom)
    (I : Finset (Fin (n + 2))) (hj : j ∉ I)
    (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq (s.hom I a b k hI ha hb hk) (t.hom I a b k hI ha hb hk) := by
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hcard : J.card = I.card := HornIndex.card_preimage I j hj
  have hJ : 2 ≤ J.card := by omega
  have him : J.image j.succAboveOrderEmb.toOrderHom = I := HornIndex.image_preimage I j hj
  let a' := J.min' (Index.nonempty hJ)
  let b' := J.max' (Index.nonempty hJ)
  have ha' : j.succAboveOrderEmb.toOrderHom a' = a := by
    rw [ha]
    simpa only [him] using Index.image_min (f := j.succAboveOrderEmb.toOrderHom)
      j.succAboveOrderEmb.monotone (J.isLeast_min' (Index.nonempty hJ))
      (Finset.Nonempty.image (Index.nonempty hJ) _)
  have hb' : j.succAboveOrderEmb.toOrderHom b' = b := by
    rw [hb]
    simpa only [him] using Index.image_max (f := j.succAboveOrderEmb.toOrderHom)
      j.succAboveOrderEmb.monotone (J.isGreatest_max' (Index.nonempty hJ))
      (Finset.Nonempty.image (Index.nonempty hJ) _)
  have hh := hom_heq_of_pullback_eq s t j.succAboveOrderEmb.toOrderHom
    j.succAboveOrderEmb.toOrderHom h J a' b' k hJ rfl rfl (by rw [hcard]; exact hk)
    j.succAboveOrderEmb.injective.injOn j.succAboveOrderEmb.injective.injOn
  cases ha'
  cases hb'
  simpa only [him] using hh

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
