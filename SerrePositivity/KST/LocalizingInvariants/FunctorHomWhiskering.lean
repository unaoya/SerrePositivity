module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

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
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (i ≫ F) (i ≫ G) :=
  (hoFunctor.map ((pre i).app X)).toFunctor.map α

def homPost {A X Y : SSet.{u}} (j : X ⟶ Y) {F G : A ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (F ≫ j) (G ≫ j) :=
  (hoFunctor.map ((ihom A).map j)).toFunctor.map α

lemma homPre_homComp {A B X : SSet.{u}} (i : A ⟶ B) {F G H : B ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G H) :
    homPre i (α ≫ β) = homPre i α ≫ homPre i β := Functor.map_comp _ _ _

lemma homPre_id {A B X : SSet.{u}} (i : A ⟶ B) (F : B ⟶ X) :
    homPre i (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

lemma homPost_homComp {A X Y : SSet.{u}} (j : X ⟶ Y) {F G H : A ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G H) :
    homPost j (α ≫ β) = homPost j α ≫ homPost j β := Functor.map_comp _ _ _

lemma homPost_id {A X Y : SSet.{u}} (j : X ⟶ Y) (F : A ⟶ X) :
    homPost j (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

lemma homPre_comp {A B C X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (j : B ⟶ C) {F G : C ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) : homPre (i ≫ j) α = homPre i (homPre j α) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom α
  rw [← h]
  unfold homPre
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom,
    ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom]
  congr 1

lemma homPost_comp {A X Y Z : SSet.{u}} [Quasicategory X]
    (i : X ⟶ Y) (j : Y ⟶ Z) {F G : A ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) : homPost (i ≫ j) α = homPost j (homPost i α) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom α
  rw [← h]
  unfold homPost
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom,
    ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
  congr 1

lemma homPre_post {A B X Y : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (j : X ⟶ Y) {F G : B ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) : homPre i (homPost j α) = homPost j (homPre i α) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom α
  rw [← h]
  unfold homPre homPost
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom,
    ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom]
  congr 1

end SerrePositivity.KST.LocalizingInvariants
