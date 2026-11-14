module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackCoconeIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMap

/-!
概要：cospan の左始域の実代数射から、経路を保つ homotopy pullback 模型の射を作る。
方針：元の二脚と同じ乗法的経路を普遍的持ち上げへ渡し、比較 cochain も回収する。
規約：元の射への指定比較を保つ。使われ方：cell 分解上の Postnikov class の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A A' B C : Mon (Complex R)}
  (f : A ⟶ B) (g : C ⟶ B) (a : A' ⟶ A)

def sourceMapWitness : Path.Witness R ((left R (a ≫ f) g ≫ a) ≫ f) (right R (a ≫ f) g ≫ g) where
  hom := path R (a ≫ f) g
  source_eq := (path_source R (a ≫ f) g).trans (Category.assoc _ _ _).symm
  target_eq := path_target R (a ≫ f) g

def sourceMap : algebra R (a ≫ f) g ⟶ algebra R f g :=
  lift R f g (left R (a ≫ f) g ≫ a) (right R (a ≫ f) g) (sourceMapWitness R f g a)

lemma sourceMap_left : sourceMap R f g a ≫ left R f g = left R (a ≫ f) g ≫ a :=
  lift_left R _ _ _ _ _
lemma sourceMap_right : sourceMap R f g a ≫ right R f g = right R (a ≫ f) g :=
  lift_right R _ _ _ _ _
lemma sourceMap_path : sourceMap R f g a ≫ path R f g = path R (a ≫ f) g :=
  lift_path R _ _ _ _ _

lemma sourceMap_primitive : (Cochain.ofHom (sourceMap R f g a).hom).comp
    (primitive R f g) (zero_add (-1)) = primitive R (a ≫ f) g := by
  change (Cochain.ofHom (sourceMap R f g a).hom).comp
    ((Cochain.ofHom (path R f g).hom).comp (Path.primitive R B) _) _ = _
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  have hp : (sourceMap R f g a).hom ≫ (path R f g).hom = (path R (a ≫ f) g).hom :=
    congrArg Mon.Hom.hom (sourceMap_path R f g a)
  rw [hp]
  rfl

def sourceSumMap : A'.X ⊞ C.X ⟶ A.X ⊞ C.X := biprod.map a.hom (𝟙 C.X)

lemma sourceDifference_comm : difference R (a ≫ f) g ≫ 𝟙 B.X =
    sourceSumMap R a ≫ difference R f g := by
  change biprod.desc (a.hom ≫ f.hom) (-g.hom) ≫ 𝟙 B.X =
    biprod.map a.hom (𝟙 C.X) ≫ biprod.desc f.hom (-g.hom)
  apply biprod.hom_ext'
  · simp
  · simp

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
