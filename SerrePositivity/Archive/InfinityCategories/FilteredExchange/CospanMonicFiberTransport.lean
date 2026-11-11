module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CospanBoundaryHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.NullHomotopyRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationHomotopyTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeLeftFibrationTransport

/-!
概要：単射な境界を持つ有限標的図式を、二入力の指定輸送と同時に一つの値へ移す。
方針：標的の底の一つの収縮を二入力へ制限し、標的ではその二輸送を境界として相対的に持ち上げる。
規約：元の二入力の全円柱と標的の境界の全円柱を厳密に保持する。
使われ方：単射境界の有限 path 近似から共通値での検出へ進む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二入力と有限標的図式を、元の境界の全輸送を保って共通の値へ移せる。
方針：底の共通収縮を二入力へ持ち上げ、単射な境界上の二つの像を標的の相対輸送に指定する。
規約：元の f・g を保持し、境界は終点でも全円柱でも厳密に一致。使われ方：指定 path の同時有限検出。 -/
lemma leftFibration_cospan_monic_fiber_transport {A C M E D H B : SSet.{u}}
    [M.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]
    (m : A ⨿ C ⟶ M) [Mono m] (r : M ⟶ H) (u : A ⟶ E) (v : C ⟶ D)
    (hm : m ≫ r = coprod.desc (u ≫ f) (v ≫ g)) :
    ∃ b : B _⦋0⦌, ∃ s : A ⟶ vertexFiber (f ≫ p) b,
      ∃ t : C ⟶ vertexFiber (g ≫ p) b, ∃ w : M ⟶ vertexFiber p b,
      ∃ Hu : SSet.Homotopy u (s ≫ vertexFiberι (f ≫ p) b),
      ∃ Hv : SSet.Homotopy v (t ≫ vertexFiberι (g ≫ p) b),
      ∃ Hr : SSet.Homotopy r (w ≫ vertexFiberι p b),
        m ≫ w = coprod.desc (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
          (t ≫ vertexFiberMap (g ≫ p) p g rfl b) ∧
        (m ▷ (Δ[1] : SSet.{u})) ≫ Hr.h = coprodCylinderMap (Hu.h ≫ f) (Hv.h ≫ g) := by
  obtain ⟨b, ⟨h⟩⟩ := exists_nullHomotopy_of_isFilteredInfinity (r ≫ p)
  have hu : ((coprod.inl : A ⟶ A ⨿ C) ≫ m) ≫ (r ≫ p) = u ≫ (f ≫ p) := by
    rw [Category.assoc, ← Category.assoc m r p, hm,
      ← Category.assoc, coprod.inl_desc, Category.assoc]
  have hv : ((coprod.inr : C ⟶ A ⨿ C) ≫ m) ≫ (r ≫ p) = v ≫ (g ≫ p) := by
    rw [Category.assoc, ← Category.assoc m r p, hm,
      ← Category.assoc, coprod.inr_desc, Category.assoc]
  obtain ⟨s, Hu, hU⟩ := leftFibration_transport_along_nullHomotopy (f ≫ p) u b
    (nullHomotopyRestriction h ((coprod.inl : A ⟶ A ⨿ C) ≫ m) hu)
  obtain ⟨t, Hv, hV⟩ := leftFibration_transport_along_nullHomotopy (g ≫ p) v b
    (nullHomotopyRestriction h ((coprod.inr : C ⟶ A ⨿ C) ≫ m) hv)
  let Hb := cospanBoundaryHomotopy p f g m r u v hm b s t Hu Hv
  have hHb : Hb.h ≫ p = (m ▷ (Δ[1] : SSet.{u})) ≫ h.h :=
    cospanBoundaryHomotopy_projection p f g m r u v hm b s t Hu Hv h.h hU hV
  obtain ⟨w, hw, Hr, hHr, _⟩ := leftFibration_transport_to_fiber_relative p m r b h
    (coprod.desc (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
      (t ≫ vertexFiberMap (g ≫ p) p g rfl b)) Hb hHb
  exact ⟨b, s, t, w, Hu, Hv, Hr, hw, hHr⟩

end SerrePositivity.InfinityCategories.F2
