module
public import SerrePositivity.DifferentialGraded.Module.CellLifting
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import SerrePositivity.DifferentialGraded.Category.ComplexHomotopyComparison
/-!
概要：全整数次数の自由 sphere からの実閉射と評価 cycle の同値の線形性を公開する。
方針：恒等射の cycle に対する既存の後合成自然性から加法・スカラー作用を回収する。
規約：元の freeSphereHomEquiv を変更しない。
使われ方：c′ の任意シフト自由入力から直和への有限係数表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma freeSphereHomEquiv_val (x : D) (n : ℤ) (M : ModuleCategory R D)
    (f : freeSphere R D x n ⟶ M) :
    (freeSphereHomEquiv R D x n M f).val =
      ((moduleEvaluation R D x).map f).f n
        (freeSphereHomEquiv R D x n (freeSphere R D x n) (𝟙 _)).val := by
  simpa only [Category.id_comp] using
    freeSphereHomEquiv_naturality_val R D x n (𝟙 (freeSphere R D x n)) f

def freeSphereClosedCycleLinearEquiv (x : D) (n : ℤ) (M : ModuleCategory R D) :
    (freeSphere R D x n ⟶ M) ≃ₗ[R]
      complexCycles R ((moduleEvaluation R D x).obj M) n where
  toEquiv := freeSphereHomEquiv R D x n M
  map_add' f g := by
    apply Subtype.ext
    change (freeSphereHomEquiv R D x n M (f + g)).val =
      (freeSphereHomEquiv R D x n M f).val + (freeSphereHomEquiv R D x n M g).val
    rw [freeSphereHomEquiv_val R D x n M (f + g),
      freeSphereHomEquiv_val R D x n M f, freeSphereHomEquiv_val R D x n M g]
    rw [Functor.map_add]
    rfl
  map_smul' r f := by
    apply Subtype.ext
    change (freeSphereHomEquiv R D x n M (r • f)).val =
      r • (freeSphereHomEquiv R D x n M f).val
    rw [freeSphereHomEquiv_val R D x n M (r • f), freeSphereHomEquiv_val R D x n M f]
    letI : (moduleEvaluation R D x).Linear R := by
      dsimp [moduleEvaluation]
      infer_instance
    rw [Functor.map_smul]
    rfl

end SerrePositivity.DifferentialGraded
