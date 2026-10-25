module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedColumnComposition
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedCoefficientAction
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.ShiftedHomCoordinates
/-!
概要：始点保存ラベルの有限係数和を実 bar への全 Hom の列へ移す。
方針：列の厳密な合成則を線形延長し、単体写像による係数押出しと前合成を照合する。
規約：同じラベル・係数加群と全斉次次数を保持する。
使われ方：普遍正規化係数の作用を実正規化段階へ接続する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

private def precompositionLinear {M N P : RightModule R D} {p q k : ℤ}
    (f : (moduleHom R D M N).X p) (hk : p + q = k) :
    (moduleHom R D N P).X q →ₗ[R] (moduleHom R D M P).X k where
  toFun g := compose R (x := M) (y := N) (z := P) g f hk
  map_add' g h := compose_add_left (A := R) (D := RightModule R D) g h f hk
  map_smul' r g := dgCoherentBarHom_compose_smul_left R D r g f hk

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarBasedColumnAction {n : ℕ} (m : ℕ) (s : I _⦋n⦌) :
    (DGCoherentBarBasedLabel.{u} n m →₀ R) →ₗ[R]
      GradedHom R (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) ((n : ℤ) - (m : ℤ)) :=
  Finsupp.linearCombination R (fun a : DGCoherentBarBasedLabel.{u} n m =>
    dgCoherentBarBasedColumn R D F (SSet.stdSimplex.objEquiv a.val) a.property s)

lemma dgCoherentBarBasedColumnAction_push {l m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌)
    (z : DGCoherentBarBasedLabel.{u} m l →₀ R) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨m, I.map f.op s⟩))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarBasedColumnAction R D F l (I.map f.op s) z)
      (dgCoherentBarBasedBlock R D F f hf s)
      (by omega : ((n : ℤ) - (m : ℤ)) + ((m : ℤ) - (l : ℤ)) = (n : ℤ) - (l : ℤ)) =
    dgCoherentBarBasedColumnAction R D F l s
      (Finsupp.mapDomain (dgCoherentBarBasedLabelPush f hf) z) := by
  have h := Finsupp.lmapDomain_linearCombination R
    (v := fun a : DGCoherentBarBasedLabel.{u} m l =>
      dgCoherentBarBasedColumn R D F (SSet.stdSimplex.objEquiv a.val) a.property (I.map f.op s))
    (v' := fun a : DGCoherentBarBasedLabel.{u} n l =>
      dgCoherentBarBasedColumn R D F (SSet.stdSimplex.objEquiv a.val) a.property s)
    (dgCoherentBarBasedLabelPush f hf)
    (precompositionLinear R D
      (M := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (N := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨m, I.map f.op s⟩))
      (P := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarBasedBlock R D F f hf s) (by omega))
    (fun a => dgCoherentBarBasedColumn_comp R D F f hf
      (SSet.stdSimplex.objEquiv a.val) a.property s)
  exact (LinearMap.congr_fun h z).symm

end SerrePositivity.InfinityCategories
