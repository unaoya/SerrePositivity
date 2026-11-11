module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarCoefficients
/-!
概要：元の全 coherent 図式の面・prefix 成分を bar の一つの次数一 Hom 要素へまとめる。
方針：各 summand の有限和を構成し、元の余積の全次数 Hom 直積同型で貼り合わせる。
規約：元の全高次成分を使う。この葉では MC 方程式・native 余極限性を主張しない。
使われ方：D-8 c2 の実 bar 微分と、単体ごとの二乗零検証。
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

def dgCoherentBarFaceColumn {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 1 :=
  (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, s⟩)
    (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ))).f 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s i)

def dgCoherentBarPrefixColumn {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 1 :=
  (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩)
    (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) h))).f 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F s k h)

def dgCoherentBarColumn : (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) →
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 1
  | ⟨0, _⟩ => 0
  | ⟨n + 1, s⟩ =>
      (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
        dgCoherentBarFaceColumn R D F s i) +
      ((n : ℤ) + 1).negOnePow • ∑ k : Fin (n + 1),
        dgCoherentBarPrefixColumn R D F s k.val (by omega)

def dgCoherentBarTheta :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 1 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) 1).symm
    (dgCoherentBarColumn R D F)

lemma dgCoherentBarTheta_restrict (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 1 (dgCoherentBarTheta R D F) =
      dgCoherentBarColumn R D F s := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv_apply]
  exact congrFun (LinearEquiv.apply_symm_apply
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) 1) (dgCoherentBarColumn R D F)) s

end SerrePositivity.InfinityCategories.Project.DerivedCategories
