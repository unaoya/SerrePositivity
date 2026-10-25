module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarCoefficients
public import SerrePositivity.InfinityCategories.DGNerve.CoherentDiagramTopBoundary
/-!
概要：元の bar prefix 係数の内部微分を、実際の HA 有限和へ同定する。
方針：元の最上成分の微分式を、同じ始点・tail 始点へ輸送する。
規約：元の全高次 Hom と端点を保持し、HA 右辺は追加の明示入力にしない。
使われ方：正次元 bar 列の MC 式における prefix の内部微分項。
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

def dgCoherentBarPrefixBoundary {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (moduleHom R D (dgCoherentBarSource R D F ⟨n, s⟩)
      (dgCoherentBarSource R D F (dgCoherentBarTail s (k + 1) h))).X (-(k : ℤ) + 1) :=
  gradedHomTransport (A := R) (D := RightModule R D)
    (dgCoherentBarSource_prefix R D F s (k + 1) h)
    (dgCoherentBarPrefix_target R D F s k h) rfl
    (coherentDiagramTopBoundary F (dgCoherentBarPrefix s (k + 1) h).2)

lemma dgCoherentBarPrefixHom_d {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (moduleHom R D (dgCoherentBarSource R D F ⟨n, s⟩)
      (dgCoherentBarSource R D F (dgCoherentBarTail s (k + 1) h))).d
        (-(k : ℤ)) (-(k : ℤ) + 1) (dgCoherentBarPrefixHom R D F s k h) =
      dgCoherentBarPrefixBoundary R D F s k h := by
  change differential R (x := dgCoherentBarSource R D F ⟨n, s⟩)
    (y := dgCoherentBarSource R D F (dgCoherentBarTail s (k + 1) h))
    (dgCoherentBarPrefixHom R D F s k h) = _
  unfold dgCoherentBarPrefixHom dgCoherentBarPrefixBoundary
  rw [← gradedHomTransport_differential, coherentDiagramTop_d]

lemma dgCoherentBarPrefixBlock_d {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarTail s (k + 1) h)))).d 1 2
      (dgCoherentBarPrefixBlock R D F s k h) =
      (-((n - (k + 1) : ℕ) : ℤ)).negOnePow •
        moduleHomShiftBlock R D (n : ℤ) ((n - (k + 1) : ℕ) : ℤ)
          (dgCoherentBarPrefixBoundary R D F s k h)
          (by omega : (n : ℤ) + (-(k : ℤ) + 1) - ((n - (k + 1) : ℕ) : ℤ) = 2) := by
  have hd := moduleHomShiftBlock_d R D (n : ℤ) ((n - (k + 1) : ℕ) : ℤ)
    (dgCoherentBarPrefixHom R D F s k h)
    (by omega : (n : ℤ) + -(k : ℤ) - ((n - (k + 1) : ℕ) : ℤ) = 1)
  have hc := congrArg (fun f :
      (moduleHom R D (dgCoherentBarSource R D F ⟨n, s⟩)
        (dgCoherentBarSource R D F (dgCoherentBarTail s (k + 1) h))).X (-(k : ℤ) + 1) =>
    moduleHomShiftBlock R D (n : ℤ) ((n - (k + 1) : ℕ) : ℤ)
      (M := dgCoherentBarSource R D F ⟨n, s⟩)
      (N := dgCoherentBarSource R D F (dgCoherentBarTail s (k + 1) h)) f
      (by omega : (n : ℤ) + (-(k : ℤ) + 1) - ((n - (k + 1) : ℕ) : ℤ) = 2))
    (dgCoherentBarPrefixHom_d R D F s k h)
  exact hd.trans (congrArg (fun z => (-((n - (k + 1) : ℕ) : ℤ)).negOnePow • z) hc)

end SerrePositivity.InfinityCategories
