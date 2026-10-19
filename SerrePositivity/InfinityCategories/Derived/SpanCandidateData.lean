module
public import SerrePositivity.InfinityCategories.Derived.SpanResidualCoordinates
public import SerrePositivity.InfinityCategories.Derived.SpanTwoPrefixIndex
public import SerrePositivity.InfinityCategories.DGNerve.ReplacementLocality

/-! # span の二未知成分の挿入

概要：後続成分と A 側成分を指定した射で置換し、既知の成分と方程式を保存する。
方針：固定一射の置換を二回適用し、後続集合を含まない集合では局所性を使う。
規約：HA Proposition 1.3.1.10。使われ方：D7 の cofiber 境界充填候補。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 後続集合に A 頂点を追加すると真に大きくなる。 -/
lemma spanFirst_insert_not_subset (n : ℕ) :
    ¬ insert (0 : Fin (n + 4)) (spanSuffixFaces n) ⊆ spanSuffixFaces n := by
  intro h
  have := (mem_spanSuffixFaces _).mp (h (Finset.mem_insert_self _ _))
  change 2 ≤ 0 at this
  omega

namespace DGNerve.SimplexData

/-- 後続集合と A を加えた集合の二成分を順に置換する。 -/
def spanInsertUnknowns {n : ℕ} (s : SimplexData R D (n + 3))
    (q : GradedHom R (s.obj (spanApex n)) (s.obj (Fin.last (n + 3))) (-(n : ℤ)))
    (a : GradedHom R (s.obj 0) (s.obj (Fin.last (n + 3))) (-(n : ℤ) - 1)) :
    SimplexData R D (n + 3) :=
  (s.replaceFixed (spanSuffixFaces n) (spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [card_spanSuffixFaces]; omega)
    (spanSuffixFaces_min n _) (spanSuffixFaces_max n _)
    (by rw [card_spanSuffixFaces]; push_cast; omega) q).replaceFixed
      (insert 0 (spanSuffixFaces n)) 0 (Fin.last (n + 3)) (-(n : ℤ) - 1)
      (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
      (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
      (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; push_cast; omega) a

variable {n : ℕ} (s : SimplexData R D (n + 3))
    (q : GradedHom R (s.obj (spanApex n)) (s.obj (Fin.last (n + 3))) (-(n : ℤ)))
    (a : GradedHom R (s.obj 0) (s.obj (Fin.last (n + 3))) (-(n : ℤ) - 1))

/-- 二つの挿入集合以外の成分は変わらない。 -/
lemma spanInsertUnknowns_hom_of_ne (I : Finset (Fin (n + 4)))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (Index.nonempty hI)) (hy : y = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hq : I ≠ spanSuffixFaces n) (ha : I ≠ insert 0 (spanSuffixFaces n)) :
    (s.spanInsertUnknowns q a).hom I x y k hI hx hy hk = s.hom I x y k hI hx hy hk := by
  unfold spanInsertUnknowns replaceFixed
  rw [replace_hom_of_ne (hne := ha), replace_hom_of_ne (hne := hq)]

/-- 後続集合の成分は指定した q と異種等号で一致する。 -/
lemma spanInsertUnknowns_suffix_heq
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (spanSuffixFaces n).card)
    (hx : x = (spanSuffixFaces n).min' (Index.nonempty hI))
    (hy : y = (spanSuffixFaces n).max' (Index.nonempty hI))
    (hk : k = 2 - ((spanSuffixFaces n).card : ℤ)) :
    HEq ((s.spanInsertUnknowns q a).hom (spanSuffixFaces n) x y k hI hx hy hk) q := by
  have hne : spanSuffixFaces n ≠ insert 0 (spanSuffixFaces n) := by
    intro h
    exact spanFirst_insert_not_subset n (h ▸ Finset.Subset.rfl)
  unfold spanInsertUnknowns replaceFixed
  rw [replace_hom_of_ne (hne := hne), replace_hom_same]
  exact fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- A を加えた集合の成分は指定した a と異種等号で一致する。 -/
lemma spanInsertUnknowns_first_heq
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (insert 0 (spanSuffixFaces n)).card)
    (hx : x = (insert 0 (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hy : y = (insert 0 (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert 0 (spanSuffixFaces n)).card : ℤ)) :
    HEq ((s.spanInsertUnknowns q a).hom (insert 0 (spanSuffixFaces n)) x y k hI hx hy hk) a := by
  unfold spanInsertUnknowns replaceFixed
  rw [replace_hom_same]
  exact fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- 後続集合を含まない集合の既知方程式は保存される。 -/
lemma spanInsertUnknowns_equation (I : Finset (Fin (n + 4)))
    (hI : ¬ spanSuffixFaces n ⊆ I) (heq : s.Equation I) :
    (s.spanInsertUnknowns q a).Equation I := by
  unfold spanInsertUnknowns replaceFixed
  apply equation_replace_of_not_subset
  · exact fun h => hI (Finset.Subset.trans (Finset.subset_insert _ _) h)
  · exact equation_replace_of_not_subset s _ _ I hI heq

/-- 後続の一点を除く既知面は二成分の挿入後も変わらない。 -/
lemma spanInsertUnknowns_pullback_face (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    (s.spanInsertUnknowns q a).pullback j.succAboveOrderEmb.toOrderHom =
      s.pullback j.succAboveOrderEmb.toOrderHom := by
  unfold spanInsertUnknowns replaceFixed
  rw [replace_pullback_of_omits _ _ _ _ j (Finset.mem_insert_of_mem hj)
      (fun x => Fin.succAbove_ne j x),
    replace_pullback_of_omits _ _ _ _ j hj (fun x => Fin.succAbove_ne j x)]

/-- 二成分挿入後の後続方程式の右辺は元の右辺に等しい。 -/
lemma spanInsertUnknowns_suffix_rhs :
    (s.spanInsertUnknowns q a).spanSuffixRhs = s.spanSuffixRhs := by
  unfold spanInsertUnknowns spanSuffixRhs
  rw [rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _ (spanFirst_insert_not_subset n),
    replaceFixed_rhs_self]

end DGNerve.SimplexData
end SerrePositivity.InfinityCategories
