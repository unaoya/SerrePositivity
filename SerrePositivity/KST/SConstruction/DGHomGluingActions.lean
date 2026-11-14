module
public import SerrePositivity.KST.SConstruction.DGHomGluingBimodule
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ActionElements

/-! # Hom gluing の実左右作用の全次数成分
概要：同じ実 gluing の左右作用を、元の標的内の通常順合成へ照合する。
方針：閉元での評価と Hom 双加群の作用公式を直接合成する。
規約：元の閉比較と符号を保持。使われ方：閉比較族の全 Hom 自然性の移送。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

/-- 左成分の実作用は、元の標的内での前合成。 -/
lemma dgHomGluingLeftAction_apply (n : ℤ) (f : GradedHom R X.left Y.left n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D _ X Y).f n f =
      forward R ((p.map X.left Y.left).f n f) Y.gluing.val (add_zero n) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction_apply R C D _ X Y n f).trans
    (dgHomGluingBimodule_rightAction R C D E p q Y.right f Y.gluing.val (zero_add n))

/-- 右成分の実作用は、元の標的内での後合成。 -/
lemma dgHomGluingRightAction_apply (n : ℤ) (g : GradedHom R X.right Y.right n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D _ X Y).f n g =
      forward R X.gluing.val ((q.map X.right Y.right).f n g) (zero_add n) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction_apply R C D _ X Y n g).trans (by
    have hh := dgHomGluingBimodule_leftAction R C D E p q X.left g X.gluing.val
      (zero_add n)
    simp only [mul_zero, Int.negOnePow_zero, one_smul] at hh
    exact hh)

end SerrePositivity.KST.SConstruction
