module
public import SerrePositivity.InfinityCategories.DGNerve.HornComponents
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra
public import SerrePositivity.InfinityCategories.DGNerve.PinchedRecoverIndex
public import SerrePositivity.InfinityCategories.DGNerve.EquationTransfer

/-!
概要：単体データの最終対象と、そこへ向かう全成分だけを取り替える。
方針：最後以外の端点の射は元の射を移送し、最後への射は指定した族を使う。
規約：方程式を追加せず、元の先頭面のデータを厳密に保持する。
使われ方：bar の包含係数を最後の対象への成分として Bianchi 恒等式に渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

def lastReplacementObj {n : ℕ} (s : SimplexData A D (n + 1)) (Y : D)
    (i : Fin (n + 2)) : D :=
  if i = Fin.last (n + 1) then Y else s.obj i

lemma lastReplacementObj_of_ne {n : ℕ} (s : SimplexData A D (n + 1)) (Y : D)
    (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
    lastReplacementObj s Y i = s.obj i := ite_eq_right hi

lemma lastReplacementObj_last {n : ℕ} (s : SimplexData A D (n + 1)) (Y : D) :
    lastReplacementObj s Y (Fin.last (n + 1)) = Y := ite_eq_left rfl

abbrev LastReplacementHom {n : ℕ} (s : SimplexData A D (n + 1)) (Y : D) :=
  ∀ (I : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hI : 2 ≤ I.card),
    a = I.min' (Index.nonempty hI) →
    Fin.last (n + 1) = I.max' (Index.nonempty hI) →
    k = 2 - (I.card : ℤ) → GradedHom A (s.obj a) Y k

def lastReplacement {n : ℕ} (s : SimplexData A D (n + 1)) (Y : D)
    (f : LastReplacementHom s Y) : SimplexData A D (n + 1) where
  obj := lastReplacementObj s Y
  hom I a b k hI ha hb hk := by
    have han : a ≠ Fin.last (n + 1) := ha ▸ PinchedHom.min_ne_last I hI
    by_cases hbLast : b = Fin.last (n + 1)
    · exact (gradedHomTransportWithHEq
        (lastReplacementObj_of_ne s Y a han).symm
        (by rw [hbLast, lastReplacementObj_last]) rfl
        (f I a k hI ha (hbLast.symm.trans hb) hk)).val
    · exact (gradedHomTransportWithHEq
        (lastReplacementObj_of_ne s Y a han).symm
        (lastReplacementObj_of_ne s Y b hbLast).symm rfl
        (s.hom I a b k hI ha hb hk)).val

lemma lastReplacement_hom_old {n : ℕ} (s : SimplexData A D (n + 1)) (Y : D)
    (f : LastReplacementHom s Y)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hbLast : b ≠ Fin.last (n + 1)) :
    HEq ((lastReplacement s Y f).hom I a b k hI ha hb hk)
      (s.hom I a b k hI ha hb hk) := by
  simp only [lastReplacement, dite_eq_right hbLast]
  exact (gradedHomTransportWithHEq _ _ _ _).property

lemma lastReplacement_hom_last {n : ℕ} (s : SimplexData A D (n + 1)) (Y : D)
    (f : LastReplacementHom s Y)
    (I : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : Fin.last (n + 1) = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq ((lastReplacement s Y f).hom I a (Fin.last (n + 1)) k hI ha hb hk)
      (f I a k hI ha hb hk) := by
  simp only [lastReplacement]
  exact (gradedHomTransportWithHEq _ _ _ _).property

lemma lastReplacement_front {n : ℕ} (s : SimplexData A D (n + 1)) (Y : D)
    (f : LastReplacementHom s Y) :
    (lastReplacement s Y f).pullback Fin.castSuccOrderEmb.toOrderHom =
      s.pullback Fin.castSuccOrderEmb.toOrderHom := by
  have hobj : ((lastReplacement s Y f).pullback Fin.castSuccOrderEmb.toOrderHom).obj =
      (s.pullback Fin.castSuccOrderEmb.toOrderHom).obj := by
    funext i
    exact lastReplacementObj_of_ne s Y i.castSucc (ne_of_lt (Fin.castSucc_lt_last i))
  apply SimplexData.ext hobj
  apply HomFamily.heq_of_pointwise hobj
  intro I a b k hI ha hb hk
  rw [pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ (Fin.castSucc_injective _).injOn,
    pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ (Fin.castSucc_injective _).injOn]
  exact lastReplacement_hom_old s Y f _ _ _ _ _ _ _ _
    (ne_of_lt (Fin.castSucc_lt_last b))


lemma lastReplacement_equation_old {n : ℕ} (s : Simplex A D (n + 1)) (Y : D)
    (f : LastReplacementHom s.toSimplexData Y)
    (J : Finset (Fin (n + 2))) (hJ : Fin.last (n + 1) ∉ J) :
    (lastReplacement s.toSimplexData Y f).Equation J := by
  have he := equation_image_of_pullback (lastReplacement s.toSimplexData Y f)
    Fin.castSuccOrderEmb.toOrderHom (s.pullback Fin.castSuccOrderEmb.toOrderHom)
    (lastReplacement_front s.toSimplexData Y f) (PinchedHom.withoutLast J)
    (Fin.castSucc_injective _).injOn
  have him : (PinchedHom.withoutLast J).image Fin.castSuccOrderEmb.toOrderHom = J := by
    change (PinchedHom.withoutLast J).image Fin.castSucc = J
    rw [PinchedHom.image_withoutLast, Finset.erase_eq_of_notMem hJ]
  simpa only [him] using he

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
