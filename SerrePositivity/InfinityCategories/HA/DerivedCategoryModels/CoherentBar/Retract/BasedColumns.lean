module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateFaceCoefficients
/-!
概要：始点保存の単体写像を実 bar への全 Hom の列に移し、元の面・退化列と照合する。
方針：既存の単位シフトブロックを直和包含に合成し、異なる次数の比較を分離する。
規約：元の係数族と端点輸送を使い、ラベルだけの等式で代用しない。
使われ方：正規化境界の面項を普遍係数の始点保存作用へ戻す。
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

lemma dgCoherentBarPostInclusion_heq_of_degrees (s t t' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I)
    (ht : t = t') {q q' : ℤ} (hq : q = q')
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F t))).X q)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F t'))).X q')
    (hfg : HEq f g) :
    HEq ((eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) t)).f q f)
      ((eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) t')).f q' g) := by
  cases hq
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPostInclusion_eq_of_heq R D F s t t' ht q f g hfg)

def dgCoherentBarBasedColumn {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    GradedHom R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) ((n : ℤ) - (m : ℤ)) :=
  (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩)
    (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨m, I.map f.op s⟩)).f ((n : ℤ) - (m : ℤ))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F f hf s)

lemma dgCoherentBarFaceColumn_based_heq {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F s i)
      (dgCoherentBarBasedColumn R D F (SimplexCategory.δ i.succ) (by
        simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove]) s) := by
  exact dgCoherentBarPostInclusion_heq_of_degrees R D F ⟨n + 1, s⟩
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ) ⟨n, I.map (SimplexCategory.δ i.succ).op s⟩ rfl
    (by omega : (1 : ℤ) = ((n + 1 : ℕ) : ℤ) - (n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s i)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F (SimplexCategory.δ i.succ) (by
      simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove]) s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceBlock_based_heq R D F s i)

lemma dgCoherentBarDegeneracyColumn_based_heq {n : ℕ} (s : I _⦋n⦌) (i : Fin (n + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyColumn R D F s i)
      (dgCoherentBarBasedColumn R D F (SimplexCategory.σ i) (by
        simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s) := by
  exact dgCoherentBarPostInclusion_heq_of_degrees R D F ⟨n, s⟩
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracy s i) ⟨n + 1, I.map (SimplexCategory.σ i).op s⟩ rfl
    (by omega : (-1 : ℤ) = (n : ℤ) - ((n + 1 : ℕ) : ℤ))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock R D F s i)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F (SimplexCategory.σ i) (by
      simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarDegeneracyBlock_based_heq R D F s i)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
