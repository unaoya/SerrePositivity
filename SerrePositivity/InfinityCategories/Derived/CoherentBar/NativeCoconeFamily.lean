module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeCocone
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeFullCoefficient
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComposite
/-!
概要：指定 native 余錐を終点固定の零単体として読み、その全 HA 成分を同定する。
方針：native section の curry と uncurry の逆則を各元単体で評価する。
規約：余錐の頂点は公開 native apex で固定する。正規化加群の型は変えない。
使われ方：標準 Hom の族と右 pinched Hom 比較の恒等成分の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

def dgCoherentBarNativeCoconePoint :
    (coconeMappingSpace F (dgCoherentBarNativeApex R D F hMC)) _⦋0⦌ :=
  ⟨dgCoherentBarNormalizedNativeCocone R D F hMC, by
    rw [InfinityCategories.PinchedHom.constant_zero]
    exact dgCoherentBarNormalizedNativeCocone_vertex R D F hMC⟩

lemma dgCoherentBarNativeCoconePoint_family {n : ℕ} (s : I _⦋n⦌) :
    dgCoherentBarCoconeFamilySimplex R D F (dgCoherentBarNativeApex R D F hMC)
      (dgCoherentBarNativeCoconePoint R D F hMC) s =
        dgCoherentBarNativeSimplex R D F hMC s := by
  have hCurry := sliceOverCurry_uncurry (dgCoherentBarNativeOverSection R D F hMC)
  have hCell := congrArg (fun g =>
    (g.app (Opposite.op ⦋n⦌) (ULift.up s)).val) hCurry
  change joinMap ((SSet.yonedaEquiv
      (X := (SSet.uliftFunctor.{max (u + 1) v, u}).obj I)).symm (ULift.up s))
      (𝟙 Δ[0]) ≫ sliceOverUncurry (dgCoherentBarNativeOverSection R D F hMC) =
    (joinStdSimplexIso n 0).hom ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarNativeSimplex R D F hMC s) at hCell
  change SSet.yonedaEquiv ((joinStdSimplexIso n 0).inv ≫
    (joinMap ((SSet.yonedaEquiv
      (X := (SSet.uliftFunctor.{max (u + 1) v, u}).obj I)).symm (ULift.up s))
      (𝟙 Δ[0]) ≫ sliceOverUncurry (dgCoherentBarNativeOverSection R D F hMC))) = _
  rw [hCell, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

lemma dgCoherentBarNativeCoconePoint_column (s : dgCoherentBarIndex I) :
    HEq (dgCoherentBarCoconeFamilyColumn R D F (dgCoherentBarNativeApex R D F hMC)
      (dgCoherentBarNativeCoconePoint R D F hMC) s)
      (dgCoherentBarNativeColumn R D F hMC s) := by
  unfold dgCoherentBarCoconeFamilyColumn
  apply (gradedHomTransport_heq _ _ _ _).trans
  rw [dgCoherentBarNativeCoconePoint_family]
  exact ((dgCoherentBarNativeSimplex R D F hMC s.2).toSimplexData.hom_heq_of_indices_degree
    (I := Finset.univ) (J := Finset.univ) (c := 0) (d := Fin.last (s.1 + 1))
    (l := -(s.1 : ℤ)) (hJ := coherentDiagramTop_card s.1)
    (hc := coherentDiagramTop_min s.1) (hd := coherentDiagramTop_max s.1)
    (hl := by simp; omega) rfl rfl rfl (by omega)).trans
      (dgCoherentBarNativeSimplex_full_hom_heq R D F hMC s.2)

lemma dgCoherentBarNativeCoconePoint_hom :
    HEq (dgCoherentBarCoconeFamilyHom R D F hMC (dgCoherentBarNativeApex R D F hMC)
      (dgCoherentBarNativeCoconePoint R D F hMC))
      (unitElement R (dgCoherentBarNormalizedModule R D F hMC)).val := by
  apply heq_of_eq
  symm
  apply dgCoherentBarCoconeFamilyHom_unique R D F hMC
    (dgCoherentBarNativeApex R D F hMC) (dgCoherentBarNativeCoconePoint R D F hMC)
    (unitElement R (dgCoherentBarNormalizedModule R D F hMC)).val
  intro s
  have hUnit := unit_compose R
    (x := dgCoherentBarSource R D F s.val)
    (y := dgCoherentBarNormalizedModule R D F hMC)
    (n := -(s.val.1 : ℤ)) (dgCoherentBarNativeColumn R D F hMC s.val)
  have hCol := dgCoherentBarNativeCoconePoint_column R D F hMC s.val
  have hDeg := dgCoherentBarHom_compose_degree_heq (R := R) (C := RightModule R D)
    (a := dgCoherentBarSource R D F s.val)
    (b := dgCoherentBarNormalizedModule R D F hMC)
    (c := dgCoherentBarNormalizedModule R D F hMC)
    (p := -(s.val.1 : ℤ)) (q := 0)
    (k := -(0 : ℤ) - (s.val.1 : ℤ)) (l := -(s.val.1 : ℤ))
    (unitElement R (dgCoherentBarNormalizedModule R D F hMC)).val
    (dgCoherentBarNativeColumn R D F hMC s.val)
    (show -(s.val.1 : ℤ) + 0 = -(0 : ℤ) - (s.val.1 : ℤ) by omega) (by omega)
  exact eq_of_heq (hDeg.trans ((heq_of_eq hUnit).trans hCol.symm))

end SerrePositivity.InfinityCategories
