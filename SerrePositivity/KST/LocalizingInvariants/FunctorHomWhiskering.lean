module

public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：元の h Fun の二胞体の前後合成の結合則と交換則を保持する。
方針：同じホモトピー代表に帰着し、円柱の射の合成を比較する。
規約：元の自然変換の類を変更しない。使われ方：局所化に沿う実随伴の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def homPre {A B X : SSet.{u}} (i : A ⟶ B) {F G : B ⟶ X}
    (α : FunctorHom F G) : FunctorHom (i ≫ F) (i ≫ G) :=
  (hoFunctor.map ((pre i).app X)).toFunctor.map α

def homPost {A X Y : SSet.{u}} (j : X ⟶ Y) {F G : A ⟶ X}
    (α : FunctorHom F G) : FunctorHom (F ≫ j) (G ≫ j) :=
  (hoFunctor.map ((ihom A).map j)).toFunctor.map α

lemma homPre_homComp {A B X : SSet.{u}} (i : A ⟶ B) {F G H : B ⟶ X}
    (α : FunctorHom F G) (β : FunctorHom G H) :
    homPre i (α ≫ β) = homPre i α ≫ homPre i β := Functor.map_comp _ _ _

lemma homPre_id {A B X : SSet.{u}} (i : A ⟶ B) (F : B ⟶ X) :
    homPre i (𝟙 (HomotopyCategory.mk (functorVertex F))) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

lemma homPost_homComp {A X Y : SSet.{u}} (j : X ⟶ Y) {F G H : A ⟶ X}
    (α : FunctorHom F G) (β : FunctorHom G H) :
    homPost j (α ≫ β) = homPost j α ≫ homPost j β := Functor.map_comp _ _ _

lemma homPost_id {A X Y : SSet.{u}} (j : X ⟶ Y) (F : A ⟶ X) :
    homPost j (𝟙 (HomotopyCategory.mk (functorVertex F))) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

lemma homPre_comp {A B C X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (j : B ⟶ C) {F G : C ⟶ X}
    (α : FunctorHom F G) : homPre (i ≫ j) α = homPre i (homPre j α) := by
  have h := functorHomHomotopy_hom α
  rw [← h]
  unfold homPre
  rw [← functorHomotopyPrecomp_hom, ← functorHomotopyPrecomp_hom,
    ← functorHomotopyPrecomp_hom]
  congr 1

lemma homPost_comp {A X Y Z : SSet.{u}} [Quasicategory X]
    (i : X ⟶ Y) (j : Y ⟶ Z) {F G : A ⟶ X}
    (α : FunctorHom F G) : homPost (i ≫ j) α = homPost j (homPost i α) := by
  have h := functorHomHomotopy_hom α
  rw [← h]
  unfold homPost
  rw [← functorHomotopyPostcomp_hom, ← functorHomotopyPostcomp_hom,
    ← functorHomotopyPostcomp_hom]
  congr 1

lemma homPre_post {A B X Y : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (j : X ⟶ Y) {F G : B ⟶ X}
    (α : FunctorHom F G) : homPre i (homPost j α) = homPost j (homPre i α) := by
  have h := functorHomHomotopy_hom α
  rw [← h]
  unfold homPre homPost
  rw [← functorHomotopyPrecomp_hom, ← functorHomotopyPostcomp_hom,
    ← functorHomotopyPostcomp_hom, ← functorHomotopyPrecomp_hom]
  congr 1

end SerrePositivity.KST.LocalizingInvariants
