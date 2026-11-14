module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanResidualCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanTwoPrefixIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ReplacementLocality

/-! # span の二未知成分の挿入

概要：後続成分と A 側成分を指定した射で置換し、既知の成分と方程式を保存する。
方針：固定一射の置換を二回適用し、後続集合を含まない集合では局所性を使う。
規約：HA Proposition 1.3.1.10。使われ方：D7 の cofiber 境界充填候補。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 後続集合に A 頂点を追加すると真に大きくなる。 -/
lemma spanFirst_insert_not_subset (n : ℕ) :
    ¬ insert (0 : Fin (n + 4)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ⊆ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
  intro h
  have := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces _).mp (h (Finset.mem_insert_self _ _))
  change 2 ≤ 0 at this
  omega

namespace DGNerve.SimplexData

/-- 後続集合と A を加えた集合の二成分を順に置換する。 -/
def spanInsertUnknowns {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D (n + 3))
    (q : GradedHom R (s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)) (s.obj (Fin.last (n + 3))) (-(n : ℤ)))
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj 0) (s.obj (Fin.last (n + 3))) (-(n : ℤ) - 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D (n + 3) :=
  (s.replaceFixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; push_cast; omega) q).replaceFixed
      (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) 0 (Fin.last (n + 3)) (-(n : ℤ) - 1)
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; push_cast; omega) a

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData (spanInsertUnknowns)


variable {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D (n + 3))
    (q : GradedHom R (s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)) (s.obj (Fin.last (n + 3))) (-(n : ℤ)))
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj 0) (s.obj (Fin.last (n + 3))) (-(n : ℤ) - 1))

/-- 二つの挿入集合以外の成分は変わらない。 -/
lemma spanInsertUnknowns_hom_of_ne (I : Finset (Fin (n + 4)))
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (hx : x = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hy : y = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hq : I ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (ha : I ≠ insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) :
    (s.spanInsertUnknowns q a).hom I x y k hI hx hy hk = s.hom I x y k hI hx hy hk := by
  unfold spanInsertUnknowns _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_of_ne (hne := ha), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_of_ne (hne := hq)]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData (spanInsertUnknowns_hom_of_ne)


/-- 後続集合の成分は指定した q と異種等号で一致する。 -/
lemma spanInsertUnknowns_suffix_heq
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card)
    (hx : x = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).card : ℤ)) :
    HEq ((s.spanInsertUnknowns q a).hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) x y k hI hx hy hk) q := by
  have hne : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ≠ insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
    intro h
    exact spanFirst_insert_not_subset n (h ▸ Finset.Subset.rfl)
  unfold spanInsertUnknowns _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_of_ne (hne := hne), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_same]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData (spanInsertUnknowns_suffix_heq)


/-- A を加えた集合の成分は指定した a と異種等号で一致する。 -/
lemma spanInsertUnknowns_first_heq
    (x y : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card)
    (hx : x = (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hy : y = (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ)) :
    HEq ((s.spanInsertUnknowns q a).hom (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) x y k hI hx hy hk) a := by
  unfold spanInsertUnknowns _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_same]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData (spanInsertUnknowns_first_heq)


/-- 後続集合を含まない集合の既知方程式は保存される。 -/
lemma spanInsertUnknowns_equation (I : Finset (Fin (n + 4)))
    (hI : ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I) (heq : s.Equation I) :
    (s.spanInsertUnknowns q a).Equation I := by
  unfold spanInsertUnknowns _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_replace_of_not_subset
  · exact fun h => hI (Finset.Subset.trans (Finset.subset_insert _ _) h)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_replace_of_not_subset s _ _ I hI heq

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData (spanInsertUnknowns_equation)


/-- 後続の一点を除く既知面は二成分の挿入後も変わらない。 -/
lemma spanInsertUnknowns_pullback_face (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (s.spanInsertUnknowns q a).pullback j.succAboveOrderEmb.toOrderHom =
      s.pullback j.succAboveOrderEmb.toOrderHom := by
  unfold spanInsertUnknowns _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_pullback_of_omits _ _ _ _ j (Finset.mem_insert_of_mem hj)
      (fun x => Fin.succAbove_ne j x),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_pullback_of_omits _ _ _ _ j hj (fun x => Fin.succAbove_ne j x)]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData (spanInsertUnknowns_pullback_face)


/-- 二成分挿入後の後続方程式の右辺は元の右辺に等しい。 -/
lemma spanInsertUnknowns_suffix_rhs :
    (s.spanInsertUnknowns q a).spanSuffixRhs = s.spanSuffixRhs := by
  unfold spanInsertUnknowns _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixRhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _ (spanFirst_insert_not_subset n),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_rhs_self]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData (spanInsertUnknowns_suffix_rhs)


end DGNerve.SimplexData
end SerrePositivity.InfinityCategories.Project.DerivedCategories
