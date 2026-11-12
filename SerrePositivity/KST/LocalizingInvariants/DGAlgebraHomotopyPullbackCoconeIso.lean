module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackLinearLift

/-!
概要：実 cospan 模型の underlying 複体は、元の二脚の差の mapping cocone と同型。
方針：二射影と元の比較 cochain で逆射を作り、三成分の一意性で二合成を検証する。
規約：複体の同型を代数の同型とは扱わない。使われ方：非分裂拡大のホモロジー比較。
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

def coconeLeft : mappingCocone (difference R f g) ⟶ A.X :=
  mappingCocone.fst (difference R f g) ≫ biprod.fst

def coconeRight : mappingCocone (difference R f g) ⟶ C.X :=
  mappingCocone.fst (difference R f g) ≫ biprod.snd

lemma cocone_boundary : δ (-1) 0 (mappingCocone.snd (difference R f g)) +
    Cochain.ofHom (coconeLeft R f g ≫ f.hom - coconeRight R f g ≫ g.hom) = 0 := by
  have hd : mappingCocone.fst (difference R f g) ≫ difference R f g =
      coconeLeft R f g ≫ f.hom - coconeRight R f g ≫ g.hom := by
    simp only [difference, coconeLeft, coconeRight, biprod.desc_eq, Preadditive.comp_add,
      Preadditive.comp_neg, Category.assoc, sub_eq_add_neg]
  rw [← hd]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary _

def fromMappingCocone : mappingCocone (difference R f g) ⟶ (algebra R f g).X :=
  complexLift R f g (coconeLeft R f g) (coconeRight R f g)
    (mappingCocone.snd (difference R f g)) (cocone_boundary R f g)

lemma fromMappingCocone_left : fromMappingCocone R f g ≫ (left R f g).hom = coconeLeft R f g :=
  complexLift_left R _ _ _ _ _ _

lemma fromMappingCocone_right :
    fromMappingCocone R f g ≫ (right R f g).hom = coconeRight R f g :=
  complexLift_right R _ _ _ _ _ _

lemma fromMappingCocone_primitive :
    (Cochain.ofHom (fromMappingCocone R f g)).comp (primitive R f g) (zero_add (-1)) =
      mappingCocone.snd (difference R f g) := complexLift_primitive R _ _ _ _ _ _

lemma fromMappingCocone_toMappingCocone :
    fromMappingCocone R f g ≫ toMappingCocone R f g = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext (difference R f g)
  · apply biprod.hom_ext
    · simp only [Category.assoc, Category.id_comp, toMappingCocone_left]
      exact fromMappingCocone_left R f g
    · simp only [Category.assoc, Category.id_comp, toMappingCocone_right]
      exact fromMappingCocone_right R f g
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      toMappingCocone_snd, fromMappingCocone_primitive, Cochain.id_comp]

lemma toMappingCocone_fromMappingCocone :
    toMappingCocone R f g ≫ fromMappingCocone R f g = 𝟙 _ := by
  apply complex_hom_ext R f g
  · rw [Category.assoc, fromMappingCocone_left]
    change toMappingCocone R f g ≫
      (mappingCocone.fst (difference R f g) ≫ biprod.fst) = 𝟙 _ ≫ (left R f g).hom
    rw [toMappingCocone_left, Category.id_comp]
  · rw [Category.assoc, fromMappingCocone_right]
    change toMappingCocone R f g ≫
      (mappingCocone.fst (difference R f g) ≫ biprod.snd) = 𝟙 _ ≫ (right R f g).hom
    rw [toMappingCocone_right, Category.id_comp]
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      fromMappingCocone_primitive, toMappingCocone_snd, Cochain.id_comp]

def complexIso : (algebra R f g).X ≅ mappingCocone (difference R f g) where
  hom := toMappingCocone R f g
  inv := fromMappingCocone R f g
  hom_inv_id := toMappingCocone_fromMappingCocone R f g
  inv_hom_id := fromMappingCocone_toMappingCocone R f g

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
