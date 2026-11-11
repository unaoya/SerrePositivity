module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedColumnComposition
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedCoefficientAction
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ShiftedHomCoordinates
/-!
概要：始点保存ラベルの有限係数和を実 bar への全 Hom の列へ移す。
方針：列の厳密な合成則を線形延長し、単体写像による係数押出しと前合成を照合する。
規約：同じラベル・係数加群と全斉次次数を保持する。
使われ方：普遍正規化係数の作用を実正規化段階へ接続する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

private def precompositionLinear {M N P : _root_.SerrePositivity.DifferentialGraded.RightModule R D} {p q k : ℤ}
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N).X p) (hk : p + q = k) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D N P).X q →ₗ[R] (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M P).X k where
  toFun g := _root_.SerrePositivity.DifferentialGraded.compose R (x := M) (y := N) (z := P) g f hk
  map_add' g h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left (A := R) (D := RightModule R D) g h f hk
  map_smul' r g := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_compose_smul_left R D r g f hk

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarBasedColumnAction {n : ℕ} (m : ℕ) (s : I _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} n m →₀ R) →ₗ[R]
      GradedHom R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) ((n : ℤ) - (m : ℤ)) :=
  Finsupp.linearCombination R (fun a : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} n m =>
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F (SSet.stdSimplex.objEquiv a.val) a.property s)

lemma dgCoherentBarBasedColumnAction_push {l m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌)
    (z : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} m l →₀ R) :
    _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨m, I.map f.op s⟩))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (dgCoherentBarBasedColumnAction R D F l (I.map f.op s) z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F f hf s)
      (by omega : ((n : ℤ) - (m : ℤ)) + ((m : ℤ) - (l : ℤ)) = (n : ℤ) - (l : ℤ)) =
    dgCoherentBarBasedColumnAction R D F l s
      (Finsupp.mapDomain (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedLabelPush f hf) z) := by
  have h := Finsupp.lmapDomain_linearCombination R
    (v := fun a : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} m l =>
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F (SSet.stdSimplex.objEquiv a.val) a.property (I.map f.op s))
    (v' := fun a : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} n l =>
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F (SSet.stdSimplex.objEquiv a.val) a.property s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedLabelPush f hf)
    (precompositionLinear R D
      (M := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (N := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨m, I.map f.op s⟩))
      (P := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F f hf s) (by omega))
    (fun a => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn_comp R D F f hf
      (SSet.stdSimplex.objEquiv a.val) a.property s)
  exact (LinearMap.congr_fun h z).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
