module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedColumns
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedComposition
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.MaurerCartanDescent
/-!
概要：始点保存写像の全 Hom の列は、次の単体写像との合成を厳密に保つ。
方針：直和包含を斉次合成の外へ出し、シフトブロックの合成則とラベルの関手則を使う。
規約：二つの中間単体と端点輸送を明示し、全次数の係数を保持する。
使われ方：面・退化の実作用を普遍的なラベル係数の合成へ戻す。
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

lemma dgCoherentBarBasedColumn_comp {l m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (hf : f.toOrderHom 0 = 0)
    (g : ⦋l⦌ ⟶ ⦋m⦌) (hg : g.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨m, I.map f.op s⟩))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F g hg (I.map f.op s))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F f hf s)
      (by omega : ((n : ℤ) - (m : ℤ)) + ((m : ℤ) - (l : ℤ)) = (n : ℤ) - (l : ℤ)) =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F (g ≫ f) (by
      change f.toOrderHom (g.toOrderHom 0) = 0
      rw [hg, hf]) s := by
  have hlabel : (⟨l, I.map g.op (I.map f.op s)⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) =
      ⟨l, I.map (g ≫ f).op s⟩ := by
    exact congrArg (fun t => (⟨l, t⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I))
      (ConcreteCategory.congr_hom (I.map_comp f.op g.op) s).symm
  have hpost := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_postcompose_comp R D
    (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩)
    (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨m, I.map f.op s⟩)
    (P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨l, I.map g.op (I.map f.op s)⟩)
    (Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
    (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨l, I.map g.op (I.map f.op s)⟩)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F f hf s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F g hg (I.map f.op s))
    (by omega : ((n : ℤ) - (m : ℤ)) + ((m : ℤ) - (l : ℤ)) = (n : ℤ) - (l : ℤ))
  have hinc := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPostInclusion_eq_of_heq R D F ⟨n, s⟩
    ⟨l, I.map g.op (I.map f.op s)⟩ ⟨l, I.map (g ≫ f).op s⟩ hlabel ((n : ℤ) - (l : ℤ))
    (_root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨m, I.map f.op s⟩))
      (z := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨l, I.map g.op (I.map f.op s)⟩))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F g hg (I.map f.op s))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F f hf s) (by omega))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F (g ≫ f) (by
      change f.toOrderHom (g.toOrderHom 0) = 0
      rw [hg, hf]) s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock_comp_heq R D F f hf g hg s)
  exact hpost.symm.trans hinc

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
