module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import SerrePositivity.AlgebraicGeometry.FppfComparisonBaseChangeDescent
public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechBaseChangeColumns
public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechBaseChangeRows
public import SerrePositivity.AlgebraicGeometry.PairedPerfectCechZeroRow
public import SerrePositivity.AlgebraicGeometry.ComplexValuedDoubleCechSymmetry
public import SerrePositivity.AlgebraicGeometry.NilBaseChangePerfectCech
public import SerrePositivity.AlgebraicGeometry.FiniteAffineCover

/-!
概要：同じ固有射の普遍降下性を、相対アフィンfppfとの合成のタプルtotalへ送る。
方針：元の有限アフィン被覆で二変数図式を作り、正次数の列と行から零次軸を比較する。
規約：合成自体の平坦性も非アフィンなΓの平坦性も仮定しない。
使われ方：相対fppf消去の元のアフィン基底での出口（承認済み計画F11）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicTopology
universe u
set_option backward.isDefEq.respectTransparency false

/-- 相対アフィンfppfと固有全射の合成の、元の単位被覆のタプルtotalは完全。 -/
theorem affine_fppf_composite_tupleTotal_acyclic
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A B : Scheme.{u}} [IsAffine A] (q : A ⟶ B)
    [IsAffineHom q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (g : B ⟶ Spec (CommRingCat.of R)) [IsProper g] [Surjective g]
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hg : PerfectCechUniversalDescent p hp g) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble (q ≫ g) (fun _ : Unit ↦ ⊤) p hp hR) (.up ℕ)).Acyclic := by
  classical
  haveI : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace g
  let 𝒰 := B.affineCover.finiteSubcover
  letI := Fintype.ofFinite 𝒰.I₀
  let e := (Fintype.equivFin 𝒰.I₀).symm
  let V (j : Fin (Fintype.card 𝒰.I₀)) : B.Opens := (𝒰.f (e j)).opensRange
  have hAff (i : 𝒰.I₀) : IsAffine (𝒰.X i) := by
    rw [B.affineCover.finiteSubcover_X]
    exact Scheme.isAffine_affineCover B _
  have hV (j) : IsAffineOpen (V j) := by
    haveI := hAff (e j)
    exact isAffineOpen_opensRange (𝒰.f (e j))
  have hcV : (⨆ j, V j) = ⊤ := (Equiv.iSup_comp e).trans 𝒰.iSup_opensRange
  let F : Arrow.mk (pullback.snd g (𝟙 (Spec (CommRingCat.of R)))) ⟶ Arrow.mk g :=
    Arrow.homMk (pullback.fst g (𝟙 _)) (𝟙 _) pullback.condition
  haveI : IsIso F.left := by change IsIso (pullback.fst g (𝟙 _)); infer_instance
  haveI : IsIso F.right := by change IsIso (𝟙 (Spec (CommRingCat.of R))); infer_instance
  have H : IsPullback F.left (pullback.snd g (𝟙 (Spec (CommRingCat.of R)))) g F.right :=
    IsPullback.of_hasPullback g (𝟙 _)
  have hbase : F.right = Spec.map (CommRingCat.ofHom (RingHom.id R)) := (Spec.map_id _).symm
  have hPCg := (nilBaseChange_tupleTotal_acyclic_iff
    (pullback.snd g (𝟙 (Spec (CommRingCat.of R)))) g F H (RingHom.id R) hbase
      p hp hR hR V hV).mpr
        (hg R hR (𝟙 _) _ (fun i ↦ F.left ⁻¹ᵁ V i)
          (fun i ↦ (hV i).preimage F.left) (F.left.iSup_preimage_eq_top hcV))
  let h := q ≫ g
  have hcol := pairedCech_col_acyclic_of_baseChangeDescent h g V hV hcV p hp hR
    (fun i _ ↦ perfectCechUniversalDescent_baseChange p hp g
      (augmentedNerveBase h (SerrePositivity.Cech.simplex i)) hg)
  have hrowInput (j : ℕ) (hj : 0 < j) : PerfectCechUniversalDescent p hp
      (pullback.snd h (augmentedNerveBase g (SerrePositivity.Cech.simplex j))) := by
    cases j with
    | zero => omega
    | succ n => exact fppfComparison_baseChange_descent q g (SimplexCategory.mk n) p hp
  have hrow := pairedCech_row_acyclic_of_baseChangeDescent h g V hV hcV p hp hR hrowInput
  let D := pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR
  have hcol0 := (pairedPerfectCech_zero_col_acyclic_iff h g (fun _ : Unit ↦ ⊤) V p hp hR).mpr hPCg
  have hrow0 := (complexValuedDoubleCech_axes_acyclic_iff D hcol hrow).mp hcol0
  exact (pairedPerfectCech_zero_row_acyclic_iff h g (fun _ : Unit ↦ ⊤) V p hp hR).mp hrow0

end SerrePositivity.AlgebraicGeometry
