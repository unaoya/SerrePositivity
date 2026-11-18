module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# 元の rank 1 disk の各次数の射影性

概要：元の Hovey disk の成分は全て射影加群。
方針：二つの支持次数では単位加群、その他では零対象を使う。
規約：全整数次数と任意可換環に適用する。
使われ方：可縮 disk 関手が全射を fibration へ送ることの検出。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma complexDisk_component_projective (n k : ℤ) : Projective ((complexDisk A n).X k) := by
  have hp : Projective (𝟙_ (ModuleCat.{u} A)) :=
    ModuleCat.projective_of_free (Module.Basis.singleton Unit A)
  by_cases h : k = n
  · subst k
    exact Projective.of_iso (complexDiskX₀ A n).symm hp
  · by_cases h' : k = n + 1
    · subst k
      exact Projective.of_iso (complexDiskX₁ A n).symm hp
    · exact (isZero_double_X _ _ k h h').projective

end SerrePositivity.ComplexLimits
