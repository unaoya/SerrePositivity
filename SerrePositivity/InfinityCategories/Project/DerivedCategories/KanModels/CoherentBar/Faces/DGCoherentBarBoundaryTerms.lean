module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarPositiveFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFiniteColumnComposition
/-!
概要：同じ bar 列の MC 左辺を、元の有限個の面・prefix 係数の境界項へ展開する。
方針：閉包含との微分可換性と、包含を通る斉次合成の展開を使う。
規約：境界項が零であることはここでは仮定も主張もしない。元の全次数 Hom を保つ。
使われ方：HA 方程式から各正次元列の MC 式を証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarBoundaryTerm {M : ModuleCategory R D} (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I)
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))).X 1) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 2 :=
  let A : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 2 :=
    (eHomWhiskerLeft (Complex R) M (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)).f 2
      ((_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))).d 1 2 f)
  let B : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 2 :=
    _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F s) f (show (1 : ℤ) + 1 = 2 from rfl)
  A + B

lemma dgCoherentBarFiniteBoundary {J : Type w} [Fintype J] {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (s : J → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) (c : J → ℤˣ)
    (f : ∀ j, (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (s j)))).X 1) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
        (∑ j, c j • (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
          (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (s j))).f 1 (f j)) +
      _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
        (∑ j, c j • (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
          (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (s j))).f 1 (f j))
        (show (1 : ℤ) + 1 = 2 from rfl) =
      ∑ j, c j • dgCoherentBarBoundaryTerm R D F (s j) (f j) := by
  have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiniteColumn_d R D (M := M) (T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
    (fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (s j))
    (fun j => Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (s j)) c f
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
      (∑ j, c j • (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (s j))).f 1 (f j)) =
    ∑ j, c j • (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (s j))).f 2
        ((_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
          (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (s j)))).d 1 2 (f j)) at hd
  rw [hd]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiniteColumn_compose R D (M := M) (T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
    (U := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) (fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (s j))
    (fun j => Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (s j)) c f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
    (show (1 : ℤ) + 1 = 2 from rfl)]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_restrict, dgCoherentBarBoundaryTerm,
    smul_add, Finset.sum_add_distrib]

lemma dgCoherentBarColumn_positive_boundary {n : ℕ} (s : I _⦋n + 1⦌) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F ⟨n + 1, s⟩) +
      compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, s⟩))
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F ⟨n + 1, s⟩)
        (show (1 : ℤ) + 1 = 2 from rfl) =
      ∑ j : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPositiveIndex n, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPositiveSign n j •
        dgCoherentBarBoundaryTerm R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPositiveTarget s j)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPositiveCoefficient R D F s j) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn_positive_coefficients R D F s]
  exact dgCoherentBarFiniteBoundary R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPositiveTarget s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPositiveSign n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPositiveCoefficient R D F s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
