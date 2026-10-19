module
public import SerrePositivity.InfinityCategories.Derived.DGCommonRoofComparisonFillers

/-! # 共通宇宙の元の屋根比較の局所有限頂点持ち上げ

概要：商側屋根の任意の有限個の係数頂点を、元の添字からの一つの細分後で持ち上げる。
方針：元の始域で零次元の相対比較を構成し、指定細分射を共通宇宙へ移す。
規約：元の係数単体を固定する。使われ方：全空間比較の連結成分上の全射性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGQuotient DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 共通添字の商側の有限係数頂点を、同じ添字からの一つの細分後で持ち上げる。 -/
theorem dgCommonRoofComparison_vertex_lifts (P : Set D) (hP : localKFlat A D P)
    {m : ℕ} (x : D) (y : Fin m → D) (c : DGCommonRoofIndex A D P x)
    (g : ∀ i, ((dgCommonRoofQuotient A D P x (y i)).obj c) _⦋0⦌) :
    ∃ d : DGCommonRoofIndex A D P x, ∃ r : c ⟶ d,
      ∃ t : ∀ i, ((dgCommonRoofOriginal A D P x (y i)).obj d) _⦋0⦌,
        ∀ i, Nonempty (RoofBoundaryFixedHomotopy
          (SSet.yonedaEquiv.symm (g i) ≫ (dgCommonRoofQuotient A D P x (y i)).map r)
          (SSet.yonedaEquiv.symm (t i) ≫ (dgCommonRoofComparison A D P x (y i)).app d)) := by
  cases c with | up c =>
    let s := c.unop
    let q := ForgetEnrichment.to (Complex A) s.obj.left
    have hfull (J : Finset (Fin 1)) (hJ : J.Nonempty) : J = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      obtain ⟨a, ha⟩ := hJ
      exact (Subsingleton.elim a j) ▸ ha
    obtain ⟨p, r, hr, t, _, hh⟩ :=
      dgQuotientFinite_exists_pinchedRelativeHomotopies A D P hP q y (fun _ => 0)
        (fun _ J _ hJ _ hne => (hne (hfull J hJ)).elim) (fun i => toLinearSimplex (g i))
        (fun _ J _ hJ _ hne => (hne (hfull J hJ)).elim)
    let d := op (dgClosedRoofRefine A D P x s r hr)
    let R := (dgClosedRoofRefineHom A D P x s r hr).op
    refine ⟨AsSmall.up.obj d, AsSmall.up.map R, fun i => (t i).toPinched, ?_⟩
    intro i
    let H := Classical.choice (hh i)
    change Nonempty (RoofBoundaryFixedHomotopy
      (SSet.yonedaEquiv.symm (g i) ≫ pinchedHomChainMap _)
      (SSet.yonedaEquiv.symm (t i).toPinched ≫ pinchedHomChainMap _))
    rw [pinchedLinearSimplexMap_yoneda, SSet.yonedaEquiv_symm_comp]
    exact ⟨⟨H.homotopy, H.boundary⟩⟩

end SerrePositivity.InfinityCategories
