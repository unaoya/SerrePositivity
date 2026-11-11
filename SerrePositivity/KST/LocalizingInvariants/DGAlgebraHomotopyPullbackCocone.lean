module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackComparison

/-!
概要：実 cospan 模型の複体を、元の二脚の差の mapping cocone へ写す。
方針：元の二射影と実乗法的経路の比較 cochain を、その符号のまま持ち上げる。
規約：比較の逆射・同型性は後続。使われ方：Postnikov 拡大のホモロジー比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)

def difference : A.X ⊞ C.X ⟶ B.X := biprod.desc f.hom (-g.hom)

def pairHom : (algebra R f g).X ⟶ A.X ⊞ C.X :=
  biprod.lift (left R f g).hom (right R f g).hom

lemma pairHom_fst : pairHom R f g ≫ biprod.fst = (left R f g).hom := biprod.lift_fst _ _

lemma pairHom_snd : pairHom R f g ≫ biprod.snd = (right R f g).hom := biprod.lift_snd _ _

lemma pairHom_difference : pairHom R f g ≫ difference R f g =
    (left R f g).hom ≫ f.hom - (right R f g).hom ≫ g.hom := by
  dsimp only [pairHom, difference]
  rw [biprod.lift_desc, Preadditive.comp_neg, sub_eq_add_neg]

def primitive : Cochain (algebra R f g).X B.X (-1) :=
  (Cochain.ofHom (path R f g).hom).comp (Path.primitive R B) (zero_add (-1))

lemma primitive_boundary : δ (-1) 0 (primitive R f g) +
    Cochain.ofHom (pairHom R f g ≫ difference R f g) = 0 := by
  have hb : δ (-1) 0 (Path.primitive R B) +
      Cochain.ofHom (Path.endpointsHom R B ≫ Path.difference R B) = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary (Path.difference R B)
  rw [Path.endpointsHom_difference] at hb
  have hs : (path R f g).hom ≫ (Path.source R B).hom =
      (left R f g).hom ≫ f.hom := congrArg Mon.Hom.hom (path_source R f g)
  have ht : (path R f g).hom ≫ (Path.target R B).hom =
      (right R f g).hom ≫ g.hom := congrArg Mon.Hom.hom (path_target R f g)
  have h := congrArg (fun z : Cochain (Path.algebra R B).X B.X 0 =>
    (Cochain.ofHom (path R f g).hom).comp z (zero_add 0)) hb
  rw [Cochain.comp_add, Cochain.comp_zero, ← δ_ofHom_comp,
    ← Cochain.ofHom_comp, Preadditive.comp_sub, hs, ht, ← pairHom_difference] at h
  exact h

def toMappingCocone : (algebra R f g).X ⟶ mappingCocone (difference R f g) :=
  mappingCocone.lift (difference R f g) (pairHom R f g) (primitive R f g)
    (primitive_boundary R f g)

@[reassoc]
lemma toMappingCocone_fst :
    toMappingCocone R f g ≫ mappingCocone.fst (difference R f g) = pairHom R f g :=
  mappingCocone.lift_fst _ _ _ _

@[reassoc]
lemma toMappingCocone_left : toMappingCocone R f g ≫
    (mappingCocone.fst (difference R f g) ≫ biprod.fst) = (left R f g).hom := by
  rw [← Category.assoc, toMappingCocone_fst, pairHom_fst]

@[reassoc]
lemma toMappingCocone_right : toMappingCocone R f g ≫
    (mappingCocone.fst (difference R f g) ≫ biprod.snd) = (right R f g).hom := by
  rw [← Category.assoc, toMappingCocone_fst, pairHom_snd]

lemma toMappingCocone_snd :
    (Cochain.ofHom (toMappingCocone R f g)).comp
      (mappingCocone.snd (difference R f g)) (zero_add (-1)) = primitive R f g := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v _ _ _ _ p q hpq

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
