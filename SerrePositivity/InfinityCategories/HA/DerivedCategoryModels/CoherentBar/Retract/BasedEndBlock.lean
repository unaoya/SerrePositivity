module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedEndColumnAction
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
/-!
概要：始点保存自己写像のブロックを零次数に固定し、列への後合成を制限で計算する。
方針：次数移送と直和包含の交換を等号の消去で示し、既存の閉包含合成則を使う。
規約：後合成する全 Hom の閉性を仮定しない。
使われ方：実境界を基底の係数列へ合成する帰納計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarPostInclusion_degree_transport (s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I)
    {p q : ℤ} (hp : p = q)
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F t))).X p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) (D := RightModule R D) rfl rfl hp
      ((eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) t)).f p f) =
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) t)).f q
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) (D := RightModule R D) rfl rfl hp f) := by
  cases hp
  rfl

def dgCoherentBarBasedEndBlock {n : ℕ} (f : ⦋n⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    GradedHom R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, I.map f.op s⟩)) 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) (D := RightModule R D) rfl rfl (sub_self (n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F f hf s)

lemma dgCoherentBarBasedEndColumn_post {n : ℕ} (f : ⦋n⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumn R D F f hf s =
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨n, I.map f.op s⟩)).f 0
      (dgCoherentBarBasedEndBlock R D F f hf s) :=
  dgCoherentBarPostInclusion_degree_transport R D F ⟨n, s⟩ ⟨n, I.map f.op s⟩
    (sub_self (n : ℤ)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F f hf s)

lemma dgCoherentBarBasedEndColumn_postcompose {n : ℕ} (f : ⦋n⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌)
    (V : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X 0) :
    _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) V
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumn R D F f hf s) rfl =
    _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, I.map f.op s⟩))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      ((eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨n, I.map f.op s⟩)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0 V)
      (dgCoherentBarBasedEndBlock R D F f hf s) rfl := by
  rw [dgCoherentBarBasedEndColumn_post, _root_.SerrePositivity.DifferentialGraded.moduleHomClosedInsertion R D]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
