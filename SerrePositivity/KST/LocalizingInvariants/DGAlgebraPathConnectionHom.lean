module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathConnectionBoundary

/-!
概要：経路から二重経路への connection を、指定比較成分を持つ実 chain map として構成。
方針：source 対角と恒等を両端にして mapping cocone に持ち上げる。
規約：この段階では乗法性を主張しない。使われ方：四辺を保つ代数 connection の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

lemma connectionHom_boundary : δ (-1) 0 (connectionCochain R B) +
    Cochain.ofHom (biprod.lift ((source R B).hom ≫ diagonalHom R B)
      (𝟙 (algebra R B).X) ≫ difference R (algebra R B)) = 0 := by
  rw [difference_eq, Preadditive.comp_sub, biprod.lift_fst, biprod.lift_snd]
  exact connectionCochain_boundary R B

/-- connection の全次数の実 chain map。乗法性は別途必要。 -/
def connectionHom : (algebra R B).X ⟶ (algebra R (algebra R B)).X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R _ _ (identityFunctor R (algebra R B))
    (identityPoint R (algebra R B)) (identityPoint R (algebra R B))
    (algebra R B).X ((source R B).hom ≫ diagonalHom R B) (𝟙 _)
    (connectionCochain R B) (connectionHom_boundary R B)

lemma connectionHom_source : connectionHom R B ≫ (source R (algebra R B)).hom =
    (source R B).hom ≫ diagonalHom R B :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_source R _ _ _ _ _ _ _ _ _ _

lemma connectionHom_target : connectionHom R B ≫ (target R (algebra R B)).hom =
    𝟙 (algebra R B).X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_replacement R _ _ _ _ _ _ _ _ _ _

lemma connectionHom_primitive :
    (Cochain.ofHom (connectionHom R B)).comp (primitive R (algebra R B))
      (zero_add (-1)) = connectionCochain R B := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v (difference R (algebra R B))
    (biprod.lift ((source R B).hom ≫ diagonalHom R B) (𝟙 _))
    (connectionCochain R B) (connectionHom_boundary R B) p q hpq

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
