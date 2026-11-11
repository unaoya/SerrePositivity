module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarCoefficients
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentDiagramTopBoundary
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarPrefixBoundary {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) h))).X (-(k : ℤ) + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) (D := _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_prefix R D F s (k + 1) h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix_target R D F s k h) rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopBoundary F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s (k + 1) h).2)

lemma dgCoherentBarPrefixHom_d {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) h))).d
        (-(k : ℤ)) (-(k : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F s k h) =
      dgCoherentBarPrefixBoundary R D F s k h := by
  change _root_.SerrePositivity.DifferentialGraded.differential R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
    (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) h))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F s k h) = _
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom dgCoherentBarPrefixBoundary
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_d]

lemma dgCoherentBarPrefixBlock_d {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) h)))).d 1 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F s k h) =
      (-((n - (k + 1) : ℕ) : ℤ)).negOnePow •
        _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D (n : ℤ) ((n - (k + 1) : ℕ) : ℤ)
          (dgCoherentBarPrefixBoundary R D F s k h)
          (by omega : (n : ℤ) + (-(k : ℤ) + 1) - ((n - (k + 1) : ℕ) : ℤ) = 2) := by
  have hd := _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock_d R D (n : ℤ) ((n - (k + 1) : ℕ) : ℤ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F s k h)
    (by omega : (n : ℤ) + -(k : ℤ) - ((n - (k + 1) : ℕ) : ℤ) = 1)
  have hc := congrArg (fun f :
      (moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) h))).X (-(k : ℤ) + 1) =>
    _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D (n : ℤ) ((n - (k + 1) : ℕ) : ℤ)
      (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
      (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) h)) f
      (by omega : (n : ℤ) + (-(k : ℤ) + 1) - ((n - (k + 1) : ℕ) : ℤ) = 2))
    (dgCoherentBarPrefixHom_d R D F s k h)
  exact hd.trans (congrArg (fun z => (-((n - (k + 1) : ℕ) : ℤ)).negOnePow • z) hc)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
