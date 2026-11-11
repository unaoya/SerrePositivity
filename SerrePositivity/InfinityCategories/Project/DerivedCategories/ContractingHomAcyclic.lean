module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingTargetHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingSourceHomotopy

/-! # 収縮対象に接する Hom 複体の非輪状性

概要：収縮対象に入る／出る Hom 複体は全整数次数で非輪状。
方針：構成した鎖ホモトピーをホモロジーに写し、恒等射が零となることを使う。
規約：基礎環の平坦性や有界性は不要。使われ方：β3 の指定対象の零化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 収縮対象へ入る Hom 複体は非輪状。 -/
lemma contractingTargetHom_acyclic (h : GradedHom A y y (-1))
    (dh : (homObject A D y y).d (-1) 0 h = (unitElement A y).val) :
    (homObject A D x y).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).2
  have hh := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingTargetHomotopy (x := x) h dh).homologyMap_eq i
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] using hh

/-- 収縮対象から出る Hom 複体は非輪状。 -/
lemma contractingSourceHom_acyclic (h : GradedHom A x x (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    (homObject A D x y).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).2
  have hh := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingSourceHomotopy (y := y) h dh).homologyMap_eq i
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] using hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
