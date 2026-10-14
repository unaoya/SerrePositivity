module

public import SerrePositivity.PerfectComplex.ClosedSupportK0
public import SerrePositivity.PerfectComplex.K0Comparison

/-! # 閉集合版 K₀ と既存の生成列版の比較

支持条件だけを変更する三角同値を作り、既存の有限自由・有限射影比較へ接続する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity

open CategoryTheory Limits Pretriangulated

variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

/-- The geometric closed support agrees with the existing scalar support on every perfect object. -/
lemma perfectHomotopySupportedOn_zeroLocus (X : PerfectHomotopy R) :
    perfectHomotopySupportedOn (supportZeroLocus (Ideal.span (Set.range z))) X ↔
      scalarSupported z X :=
  (perfectHomotopy_supported_iff_homologySupport z X).symm

/-- Change scalar support to closed support without changing the underlying perfect object. -/
def supportedPerfectToClosed : SupportedPerfectHomotopy z ⥤
    SupportedPerfectHomotopyOn (supportZeroLocus (Ideal.span (Set.range z))) :=
  (perfectHomotopySupportedOn _).lift (supportedPerfectInclusion z)
    (fun X ↦ (perfectHomotopySupportedOn_zeroLocus z X.obj).mpr X.property)

/-- Change closed support to scalar support without changing the underlying perfect object. -/
def supportedPerfectFromClosed :
    SupportedPerfectHomotopyOn (supportZeroLocus (Ideal.span (Set.range z))) ⥤
      SupportedPerfectHomotopy z :=
  (scalarSupported z).lift (supportedPerfectOnInclusion _)
    (fun X ↦ (perfectHomotopySupportedOn_zeroLocus z X.obj).mp X.property)

instance : (supportedPerfectToClosed z).CommShift ℤ := by
  dsimp only [supportedPerfectToClosed]
  infer_instance

instance : (supportedPerfectToClosed z).IsTriangulated := by
  dsimp only [supportedPerfectToClosed]
  infer_instance

instance : (supportedPerfectFromClosed z).CommShift ℤ := by
  dsimp only [supportedPerfectFromClosed]
  infer_instance

instance : (supportedPerfectFromClosed z).IsTriangulated := by
  dsimp only [supportedPerfectFromClosed]
  infer_instance

/-- The two support presentations give equivalent categories. -/
def supportedPerfectClosedEquivalence : SupportedPerfectHomotopy z ≌
    SupportedPerfectHomotopyOn (supportZeroLocus (Ideal.span (Set.range z))) where
  functor := supportedPerfectToClosed z
  inverse := supportedPerfectFromClosed z
  unitIso := NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _))
    (fun _ ↦ by ext; simp [supportedPerfectToClosed, supportedPerfectFromClosed])
  counitIso := NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _))
    (fun _ ↦ by ext; simp [supportedPerfectToClosed, supportedPerfectFromClosed])

/-- Additive equivalence between the two finite-projective support presentations. -/
def scalarClosedSupportK0Equiv : TriangulatedK0 (SupportedPerfectHomotopy z) ≃+
    K0WithSupport (supportZeroLocus (Ideal.span (Set.range z))) where
  toFun := TriangulatedK0.map (supportedPerfectToClosed z)
  invFun := TriangulatedK0.map (supportedPerfectFromClosed z)
  left_inv x := by
    have h : (TriangulatedK0.map (supportedPerfectFromClosed z)).comp
        (TriangulatedK0.map (supportedPerfectToClosed z)) = AddMonoidHom.id _ := by
      apply TriangulatedK0.hom_ext
      intro X
      simp only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk, AddMonoidHom.id_apply]
      exact TriangulatedK0.mk_iso (ObjectProperty.isoMk _ (Iso.refl _))
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : (TriangulatedK0.map (supportedPerfectToClosed z)).comp
        (TriangulatedK0.map (supportedPerfectFromClosed z)) = AddMonoidHom.id _ := by
      apply TriangulatedK0.hom_ext
      intro X
      simp only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk, AddMonoidHom.id_apply]
      exact TriangulatedK0.mk_iso (ObjectProperty.isoMk _ (Iso.refl _))
    exact DFunLike.congr_fun h x
  map_add' := (TriangulatedK0.map (supportedPerfectToClosed z)).map_add

@[simp] lemma scalarClosedSupportK0Equiv_mk (X : SupportedPerfectHomotopy z) :
    scalarClosedSupportK0Equiv z (TriangulatedK0.mk X) =
      K0WithSupport.mk _ ((supportedPerfectToClosed z).obj X) := TriangulatedK0.map_mk ..

/-- At arbitrary rings the existing free model maps to closed-support perfect K₀. -/
def freeToClosedSupportK0 : K0Supported R z →+
    K0WithSupport (supportZeroLocus (Ideal.span (Set.range z))) :=
  (scalarClosedSupportK0Equiv z).toAddMonoidHom.comp freeToPerfectK0

@[simp] lemma freeToClosedSupportK0_mk (P : PerfSupp R z) :
    freeToClosedSupportK0 z (K0.mk P) =
      K0WithSupport.mk _ ((supportedPerfectToClosed z).obj (perfSuppHomotopyObj P)) := by
  simp [freeToClosedSupportK0]

/-- Over local rings the existing finite-free K₀ is the closed-support finite-projective K₀. -/
def freeClosedSupportK0Equiv [IsLocalRing R] : K0Supported R z ≃+
    K0WithSupport (supportZeroLocus (Ideal.span (Set.range z))) :=
  (freePerfectK0Equiv (z := z)).trans (scalarClosedSupportK0Equiv z)

@[simp] lemma freeClosedSupportK0Equiv_apply [IsLocalRing R] (x : K0Supported R z) :
    freeClosedSupportK0Equiv z x = freeToClosedSupportK0 z x := rfl

end SerrePositivity
