module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDenominators
public import SerrePositivity.InfinityCategories.Stable.FiniteCofiberDenominators
public import SerrePositivity.InfinityCategories.Stable.FiniteCofiberEqualization
public import SerrePositivity.InfinityCategories.Stable.StableHoGeneration

/-! # 元の dg 圏の対象による有限共通分母

概要：前三角 dg 圏の有限個の実 Verdier 分母と等式を、元の対象から同時に細分する。
方針：実安定閉包の一般計算を native nerve に適用し、共通始点を dg 対象へ戻す。
規約：局所代表や元の Hom の平坦性を仮定しない。使われ方：商の分数表示の有限比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

local instance : IsStable (dgNerve A D) := dgNerve_isStable_of_pretriangulated A D

/-- Native nerve の実 Verdier 分母は h C の実安定閉包の三角的分母と一致する。 -/
theorem dgVerdierEdges_iff_trW (P : Set D) {x y : (dgNerve A D) _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj (dgNerve A D)) x y) :
    f.edge ∈ dgVerdierEdges A D P ↔
      (stableHoClosure (X := dgNerve A D) (Simplex.vertex '' P)).trW
        (SSet.Truncated.HomotopyCategory.homMk f) := by
  let := dgNerve_isStable_of_pretriangulated A D
  exact cofiberStableEdges_iff_trW (X := dgNerve A D) _ f

/-- 有限個の実 Verdier 分母は、元の dg 対象を共通始点とする分母で同時に細分できる。 -/
theorem dgVerdierEdges_commonDenominator (P : Set D) {n : ℕ} {x : D} (y : Fin n → D)
    (s : ∀ i, Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex (y i)) (Simplex.vertex x))
    (hs : ∀ i, (s i).edge ∈ dgVerdierEdges A D P) :
    ∃ (q : D) (t : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex q) (Simplex.vertex x)), t.edge ∈ dgVerdierEdges A D P ∧
      ∃ r : ∀ i, Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
        (Simplex.vertex q) (Simplex.vertex (y i)),
        ∀ i, (r i).edge ∈ dgVerdierEdges A D P ∧
          Nonempty (Truncated.Edge.CompStruct (r i) (s i) t) := by
  let := dgNerve_isStable_of_pretriangulated A D
  obtain ⟨q, t, ht, r, hr⟩ := cofiberStableEdges_commonDenominator (X := dgNerve A D)
    (Simplex.vertex '' P) (fun i => Simplex.vertex (y i)) s hs
  obtain ⟨q, rfl⟩ := Simplex.vertexEquiv.symm.surjective q
  exact ⟨q, t, ht, r, hr⟩

/-- 分母の後で一致する有限族を、元の dg 対象からの実分母と共有合成辺で均等化。 -/
theorem dgVerdierEdges_equalizeFinite (P : Set D) {n : ℕ} {x : D} {y z : Fin n → D}
    (f g : ∀ i, Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex x) (Simplex.vertex (y i)))
    (s : ∀ i, Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex (y i)) (Simplex.vertex (z i)))
    (hs : ∀ i, (s i).edge ∈ dgVerdierEdges A D P)
    (h : ∀ i, SSet.Truncated.HomotopyCategory.homMk (f i) ≫
      SSet.Truncated.HomotopyCategory.homMk (s i) =
      SSet.Truncated.HomotopyCategory.homMk (g i) ≫
        SSet.Truncated.HomotopyCategory.homMk (s i)) :
    ∃ (q : D) (t : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex q) (Simplex.vertex x)), t.edge ∈ dgVerdierEdges A D P ∧
      ∃ k : ∀ i, Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
        (Simplex.vertex q) (Simplex.vertex (y i)),
        ∀ i, Nonempty (Truncated.Edge.CompStruct t (f i) (k i)) ∧
          Nonempty (Truncated.Edge.CompStruct t (g i) (k i)) := by
  let := dgNerve_isStable_of_pretriangulated A D
  obtain ⟨q, t, ht, k, hk⟩ := cofiberStableEdges_equalizeFinite (X := dgNerve A D)
    (Simplex.vertex '' P) f g s hs h
  obtain ⟨q, rfl⟩ := Simplex.vertexEquiv.symm.surjective q
  exact ⟨q, t, ht, k, hk⟩

end SerrePositivity.InfinityCategories
