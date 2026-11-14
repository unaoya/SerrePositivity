module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentDiagramVertices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleCoproductHomDegrees
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
/-!
概要：元の coherent dg 加群図式の全単体を保持する bar の graded 直和。
方針：各 n 単体の始点加群を n シフトし、同じ単体のラベルで余積を取る。
規約：まだ bar 微分や native 余極限性は主張しない。元の高次図式を h 圏へ落とさない。
使われ方：D-8 c2 の bar 微分と全 Hom の係数構成。
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

/-- 次元を含む、元の図式の全単体ラベル。 -/
abbrev dgCoherentBarIndex (I : SSet.{u}) := Σ n : ℕ, I _⦋n⦌

def dgCoherentBarSource (s : dgCoherentBarIndex I) : _root_.SerrePositivity.DifferentialGraded.RightModule R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex F (I.map (SimplexCategory.const ⦋0⦌ ⦋s.1⦌ 0).op s.2)

def dgCoherentBarFamily (s : dgCoherentBarIndex I) : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D :=
  ForgetEnrichment.of (Complex R) (shiftModule (s.1 : ℤ) (dgCoherentBarSource R D F s))

abbrev dgCoherentBarGraded : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D := ∐ dgCoherentBarFamily R D F

/-- bar の各 summand からの全次数 Hom 族は、同じ直和からの一つの Hom 要素になる。 -/
def dgCoherentBarHomEquiv (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (k : ℤ) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) N)).X k ≃ₗ[R]
      (∀ s : dgCoherentBarIndex I,
        (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
          (ForgetEnrichment.to (Complex R) N)).X k) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductHomDegreeIso R D (dgCoherentBarFamily R D F) N k).toLinearEquiv

lemma dgCoherentBarHomEquiv_apply (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (k : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) N)).X k) (s : dgCoherentBarIndex I) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F N k z s =
      (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s) N).f k z := by
  exact ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductHomDegreeIso_π R D (dgCoherentBarFamily R D F) N k s) z

end SerrePositivity.InfinityCategories.Project.DerivedCategories
