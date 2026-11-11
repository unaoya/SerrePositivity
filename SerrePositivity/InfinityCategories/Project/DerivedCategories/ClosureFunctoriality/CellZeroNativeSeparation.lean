module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroObstruction
public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import SerrePositivity.KST.SConstruction.DGFunctorNativeComposition

/-!
概要：零入力の反例が、native core 間の SSet 射の反例ではないことを検証する。
方針：零入力の自己関手は恒等関手だけなので、指定頂点への定値 SSet 射を使う。
規約：零入力のみの診断。任意入力の工程 1 や最終 map の構成とは数えない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits DifferentialGraded KST.SConstruction
open DGCategoryCellResolution
open scoped _root_.Simplicial ZeroObject
variable (R : Type u) [CommRing R] [Nontrivial R]

/-- 零入力の唯一の自己関手は恒等関手。 -/
lemma cellZeroInputFunctor_eq_id (F : DGFunctor R _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v} _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v}) :
    F = DGFunctor.id _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v} := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => Subsingleton.elim _ _)
  intro x y
  exact (isZero_zero (Complex R)).eq_of_tgt _ _

/-- dg 関手型は不可能だが、同じ頂点作用の native SSet 射は零入力で存在する。 -/
def dgCellZeroNativeHom :
    dgFunctorNativeMappingSpace R _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v} _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v} ⟶
      dgFunctorNativeMappingSpace R (Source R _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v}) (Source R _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v}) :=
  SSet.const (dgFunctorNativeMappingVertex R _ _ (DGFunctor.id (Source R _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v})))

/-- 零入力においても、頂点は正本 comparisonFunctor と厳密に一致する。 -/
lemma dgCellZeroNativeHom_vertex (F : DGFunctor R _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v} _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v}) :
    (dgCellZeroNativeHom R).app (Opposite.op ⦋0⦌)
        (dgFunctorNativeMappingVertex R _ _ F) =
      dgFunctorNativeMappingVertex R _ _
        (comparisonFunctor R _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v} _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellZeroInput.{v} F) := by
  rw [cellZeroInputFunctor_eq_id R F, comparisonFunctor_identity]
  simp [dgCellZeroNativeHom, SSet.const]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
