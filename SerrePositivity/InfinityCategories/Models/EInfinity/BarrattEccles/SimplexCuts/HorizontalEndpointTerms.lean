module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalDeletionCoordinates
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalVertexKinds
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleFirstFace

/-!
模型。文献の定義との比較は後で
# 水平な始端と終端の元の境界項

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
既存の端点の座標公式を同じ削除列・実テンソル・符号の比較へ接続する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C199：水平削除の指定座標から、元の境界項の厳密な比較を得る。 -/
lemma outputBoundaryTerm_horizontal_of_coordinates {m q r : ℕ} (S : SSet.{0})
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2)) (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2)) (hk : s.horizontal k = a)
    (hsingle : ∀ l, s.horizontal l = a → l = k)
    (hw : w.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val a)
    (hh : ∀ l : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        a.succAbove (t.horizontal l))
    (hv : ∀ l : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) = t.vertical l)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) + 1))
    (hj : j.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) k) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) j x =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v.val a •
        (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).X z)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalDeletion_degree_eq (q := q) w))).hom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S t w x) := by
  have hl : ∀ c, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList s v.val k c = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList t w.val c := by
    intro c
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList_eq_selectColor,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedTrace_eq_of_horizontal_coordinates s t v.val k a hh hv,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList_eq_selectColor, hw]
  have hd := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_of_deleted_vertexLists s t v w k hl
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_horizontal_of_coordinates s t v w a k hk hsingle hd
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_of_horizontal_deleted_coordinates s t k a hk hh hv) hw (by
      intro l
      rw [hw]
      change v.val (s.horizontal (k.succAbove l)) =
        v.val (a.succAbove (t.horizontal (Fin.cast (by omega) l)))
      have hc : Fin.cast (by omega : m + q + 1 = m + 1 + q)
          (Fin.cast (by omega : m + 1 + q = m + q + 1) l) = l := Fin.ext rfl
      exact congrArg v.val (by simpa only [hc] using hh (Fin.cast (by omega) l)))
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm
  rw [dite_eq_left hd, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySign_eq_at_of_rank s v k j hj, hs,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutTensor_eq_small_cutTensorAt A S s t v w k hd hl j hj x
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalDeletion_degree_eq (q := q) w)]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm, map_zsmul, mul_smul]

/-- C200：水平始端の元の境界項は、最初の文字を削除した切断項。 -/
lemma outputBoundaryTerm_horizontal_first {m q r : ℕ} (S : SSet.{0})
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (h₀ : (0 : Fin (m + 1 + q)) ∈ s.val)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2)) (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (hw : w.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val 0)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val 0) + 1))
    (hj : j.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val 0) 0) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val 0) j x =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v.val 0 •
        (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).X z)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalDeletion_degree_eq (q := q) w))).hom
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S ((_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalInsertionEquiv m q 0).symm ⟨s, h₀⟩) w x) := by
  have hsingle := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_fiber_singleton_iff s 0).mpr
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalVertex_zero_iff s (by omega)).mpr h₀)
  refine _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm_horizontal_of_coordinates A S s _ v w 0 0
    s.horizontal_endpoints.1
    (by simpa only [s.horizontal_endpoints.1] using hsingle) hw ?_ ?_ j hj x
  · intro l
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) l) = l := Fin.ext rfl
    simpa only [Fin.succAbove_zero, hc] using _root_.SerrePositivity.EInfinity.BarrattEccles.horizontalDeletion_first_horizontal
      s h₀ (Fin.cast (by omega) l)
  · intro l
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) l) = l := Fin.ext rfl
    simpa only [Fin.succAbove_zero, hc] using _root_.SerrePositivity.EInfinity.BarrattEccles.horizontalDeletion_first_vertical
      s h₀ (Fin.cast (by omega) l)

/-- C201：水平終端の元の境界項は、最後の文字を削除した切断項。 -/
lemma outputBoundaryTerm_horizontal_last {m q r : ℕ} (S : SSet.{0})
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (a : Fin (m + 1 + q)) (ha : a ∈ s.val)
    (hlast : a.val + 1 = m + 1 + q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2)) (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (hw : w.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val (Fin.last (m + 1)))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val (Fin.last (m + 1 + q))) + 1))
    (hj : j.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val (Fin.last (m + 1 + q)))
      (Fin.last (m + 1 + q))) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val (Fin.last (m + 1 + q))) j x =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v.val (Fin.last (m + 1)) •
        (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).X z)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalDeletion_degree_eq (q := q) w))).hom
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S ((_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x) := by
  have hk : a.succ = Fin.last (m + 1 + q) := Fin.ext hlast
  have he : (⟨m + 1 + q - 1, by omega⟩ : Fin (m + 1 + q)) = a := by
    apply Fin.ext
    change m + 1 + q - 1 = a.val
    omega
  have hH : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalVertex s (Fin.last (m + 1 + q)) :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalVertex_last_iff s (by omega)).mpr (by simpa only [he] using ha)
  have hsingle := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_fiber_singleton_iff s (Fin.last (m + 1 + q))).mpr hH
  refine _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm_horizontal_of_coordinates A S s _ v w _ _
    s.horizontal_endpoints.2
    (by simpa only [s.horizontal_endpoints.2] using hsingle) hw ?_ ?_ j hj x
  · intro l
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) l) = l := Fin.ext rfl
    simpa only [hk, hc] using _root_.SerrePositivity.EInfinity.BarrattEccles.horizontalDeletion_last s a ha hlast
      (Fin.cast (by omega) l)
  · intro l
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) l) = l := Fin.ext rfl
    simpa only [hk, hc] using _root_.SerrePositivity.EInfinity.BarrattEccles.horizontalDeletion_vertical s a ha
      (Fin.cast (by omega) l)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
