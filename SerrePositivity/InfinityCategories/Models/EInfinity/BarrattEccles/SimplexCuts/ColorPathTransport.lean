module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalVertexCoordinates
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.FaceDataOrderTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceOrder
public import Mathlib.Order.Hom.Set

/-!
模型。文献の定義との比較は後で
# 色の出現位置の順序同値を元の切断の頂点へ移す

Berger–Fresse §2.2.6、M14 L12a の指定面の照合。
同じ両端を持つ区間を、元の高さを変えずに読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 同じ区間の両端を持つ出現位置への移送（BF §2.2.6 の照合の補助）。 -/
def colorPathMap {m m' q r r' : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m' q)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r' (m' + 1))
    (a : Fin r) (b : Fin r')
    (e : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val a) ≃o ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v.val b))
    (hl : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo t (e p).val)
    (hr : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t (e p).val)
    (x : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a)) : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions t v.val b) := by
  let p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val a) :=
    ⟨s.horizontal x.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp x.property).2⟩⟩
  let y := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition (e p).val (s.vertical x.val)
  have hcoord := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinates_of_interval t (e p).val (s.vertical x.val)
    (by rw [← hl p]; exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_vertical s _ x.val rfl)
    (by rw [← hr p]; exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi s _ x.val rfl)
  exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    change v.val (t.horizontal y) = b
    rw [hcoord.1]
    exact (Finset.mem_filter.mp (e p).property).2⟩⟩

/-- 上の移送は指定した二座標を持つ（BF §2.2.6 の照合の補助）。 -/
lemma colorPathMap_coordinates {m m' q r r' : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m' q)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r' (m' + 1))
    (a : Fin r) (b : Fin r')
    (e : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val a) ≃o ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v.val b))
    (hl : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo t (e p).val)
    (hr : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t (e p).val)
    (x : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a)) :
    t.horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap s t u v a b e hl hr x).val =
        (e ⟨s.horizontal x.val, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp x.property).2⟩⟩).val ∧
      t.vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap s t u v a b e hl hr x).val = s.vertical x.val := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinates_of_interval
  · rw [← hl]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_vertical s _ x.val rfl
  · rw [← hr]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi s _ x.val rfl

/-- 元の順序は同じ区間の移送で狭義に保たれる（BF §2.2.6 の照合の補助）。 -/
lemma colorPathMap_strictMono {m m' q r r' : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m' q)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r' (m' + 1))
    (a : Fin r) (b : Fin r')
    (e : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val a) ≃o ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v.val b))
    (hl : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo t (e p).val)
    (hr : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t (e p).val) :
    StrictMono (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap s t u v a b e hl hr) := by
  intro x y hxy
  have hx := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap_coordinates s t u v a b e hl hr x
  have hy := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap_coordinates s t u v a b e hl hr y
  have hhor := s.horizontal.monotone (show x.val ≤ y.val from hxy.le)
  by_contra h
  have hrev : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap s t u v a b e hl hr y).val ≤
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap s t u v a b e hl hr x).val := le_of_not_gt h
  have hth := t.horizontal.monotone hrev
  rw [hx.1, hy.1] at hth
  have hsh : s.horizontal y.val ≤ s.horizontal x.val :=
    show (⟨s.horizontal y.val, _⟩ : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val a)) ≤
      ⟨s.horizontal x.val, _⟩ from e.le_iff_le.mp hth
  have hsame := le_antisymm hhor hsh
  have htv := t.vertical.monotone hrev
  rw [hx.2, hy.2] at htv
  have hsx := s.coordinate_sum x.val
  have hsy := s.coordinate_sum y.val
  have hvals := congrArg Fin.val hsame
  have hvert : (s.vertical y.val).val ≤ (s.vertical x.val).val := htv
  have hlt : x.val.val < y.val.val := hxy
  omega

/-- C451の区間ごとの移送は、全頂点の順序同値を与える（BF §2.2.6）。 -/
def colorPathOrderIso {m m' q r r' : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m' q)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r' (m' + 1))
    (a : Fin r) (b : Fin r')
    (e : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val a) ≃o ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v.val b))
    (hl : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo t (e p).val)
    (hr : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t (e p).val) :
    ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a) ≃o ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions t v.val b) := by
  apply StrictMono.orderIsoOfSurjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap s t u v a b e hl hr)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap_strictMono s t u v a b e hl hr)
  intro y
  let z : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v.val b) :=
    ⟨t.horizontal y.val, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp y.property).2⟩⟩
  let p := e.symm z
  have hp : e p = z := e.apply_symm_apply z
  have hleft : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p.val ≤ (t.vertical y.val).val := by
    rw [hl, hp]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_vertical t _ y.val rfl
  have hright : (t.vertical y.val).val ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p.val := by
    rw [hr, hp]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi t _ y.val rfl
  have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinates_of_interval s p.val (t.vertical y.val) hleft hright
  let x : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p.val (t.vertical y.val), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by
        change u.val (s.horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p.val (t.vertical y.val))) = a
        rw [hc.1]
        exact (Finset.mem_filter.mp p.property).2⟩⟩
  refine ⟨x, ?_⟩
  have hx := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap_coordinates s t u v a b e hl hr x
  apply Subtype.ext
  apply t.vertex_injective
  apply Prod.ext
  · change t.horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap s t u v a b e hl hr x).val = t.horizontal y.val
    rw [hx.1]
    have he : (⟨s.horizontal x.val, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp x.property).2⟩⟩ :
        ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val a)) = p :=
      Subtype.ext hc.1
    rw [he, hp]
  · exact hx.2.trans hc.2

/-- 同じ全頂点の順序同値は元の高さを保つ（BF §2.2.6）。 -/
lemma colorPathOrderIso_vertical {m m' q r r' : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m' q)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r' (m' + 1))
    (a : Fin r) (b : Fin r')
    (e : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val a) ≃o ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v.val b))
    (hl : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo t (e p).val)
    (hr : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t (e p).val)
    (x : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a)) :
    t.vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathOrderIso s t u v a b e hl hr x).val = s.vertical x.val :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPathMap_coordinates s t u v a b e hl hr x).2

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
