module

public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackUniversal
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor

/-!
概要：任意の実 dg 代数射を、実経路代数の pullback により因子分解する。
方針：始点評価を底変更し、元の射に沿う対角と target 評価を使う。
規約：後半の次数全射性は後続。使われ方：導来 pullback の実模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} (f : A ⟶ B)

def algebra : Mon (Complex R) := MonoidPullback.obj (Path.source R B) f

def inclusion : algebra R f ⟶ Path.algebra R B := MonoidPullback.fst (Path.source R B) f

def projection : algebra R f ⟶ A := MonoidPullback.snd (Path.source R B) f

lemma condition : inclusion R f ≫ Path.source R B = projection R f ≫ f :=
  MonoidPullback.condition _ _

def target : algebra R f ⟶ B := inclusion R f ≫ Path.target R B

def section_ : A ⟶ algebra R f :=
  MonoidPullback.lift (Path.source R B) f (f ≫ Path.diagonal R B) (𝟙 A)
    (by rw [Category.assoc, Path.diagonal_source, Category.comp_id, Category.id_comp])

@[reassoc]
lemma section_inclusion : section_ R f ≫ inclusion R f = f ≫ Path.diagonal R B :=
  MonoidPullback.lift_fst _ _ _ _ _

@[reassoc]
lemma section_projection : section_ R f ≫ projection R f = 𝟙 A :=
  MonoidPullback.lift_snd _ _ _ _ _

lemma section_target : section_ R f ≫ target R f = f := by
  rw [target, ← Category.assoc, section_inclusion, Category.assoc,
    Path.diagonal_target, Category.comp_id]

def lift {W : Mon (Complex R)} (h : W ⟶ Path.algebra R B) (a : W ⟶ A)
    (w : h ≫ Path.source R B = a ≫ f) : W ⟶ algebra R f :=
  MonoidPullback.lift (Path.source R B) f h a w

@[reassoc]
lemma lift_inclusion {W : Mon (Complex R)} (h : W ⟶ Path.algebra R B) (a : W ⟶ A)
    (w : h ≫ Path.source R B = a ≫ f) : lift R f h a w ≫ inclusion R f = h :=
  MonoidPullback.lift_fst _ _ _ _ _

@[reassoc]
lemma lift_projection {W : Mon (Complex R)} (h : W ⟶ Path.algebra R B) (a : W ⟶ A)
    (w : h ≫ Path.source R B = a ≫ f) : lift R f h a w ≫ projection R f = a :=
  MonoidPullback.lift_snd _ _ _ _ _

lemma lift_target {W : Mon (Complex R)} (h : W ⟶ Path.algebra R B) (a : W ⟶ A)
    (w : h ≫ Path.source R B = a ≫ f) : lift R f h a w ≫ target R f = h ≫ Path.target R B := by
  rw [target, ← Category.assoc, lift_inclusion]

lemma hom_ext {W : Mon (Complex R)} {u v : W ⟶ algebra R f}
    (ha : u ≫ inclusion R f = v ≫ inclusion R f)
    (hb : u ≫ projection R f = v ≫ projection R f) : u = v :=
  MonoidPullback.hom_ext (Path.source R B) f ha hb

def cone : Limits.PullbackCone (Path.source R B) f := MonoidPullback.cone _ _

def isLimit : Limits.IsLimit (cone R f) := MonoidPullback.isLimit _ _

def pathWitness : Path.Witness R (projection R f ≫ f) (target R f) where
  hom := inclusion R f
  source_eq := condition R f
  target_eq := rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
