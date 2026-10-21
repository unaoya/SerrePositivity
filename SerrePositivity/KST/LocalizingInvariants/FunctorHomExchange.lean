module

public import SerrePositivity.KST.LocalizingInvariants.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.F1B.EnrichedPrecomposition
public import SerrePositivity.InfinityCategories.F1B.EnrichedPostcomposition

/-!
概要：h Fun の二つの自然変換の交換則。
方針：QCat の双圏の交換則を内部 Hom の前後合成へ移す。
規約：自然変換の可逆性を仮定しない。使われ方：指定した cofiber 右辺と単位の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

local instance (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

lemma homPost_homPre_exchange {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F F' : A ⟶ X} {G G' : X ⟶ Y} (α : FunctorHom F F') (β : FunctorHom G G') :
    homPost G α ≫ homPre F' β = homPre F β ≫ homPost G' α := by
  obtain ⟨α', rfl⟩ := (qcatCellEquiv F F').surjective α
  obtain ⟨β', rfl⟩ := (qcatCellEquiv G G').surjective β
  unfold homPost homPre
  rw [← qcatCell_whiskerRight, ← qcatCell_whiskerLeft,
    ← qcatCell_whiskerLeft, ← qcatCell_whiskerRight]
  change (qcatHomFunctor A Y).map (α' ▷ qcatMap G) ≫
    (qcatHomFunctor A Y).map (qcatMap F' ◁ β') =
      (qcatHomFunctor A Y).map (qcatMap F ◁ β') ≫
        (qcatHomFunctor A Y).map (α' ▷ qcatMap G')
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    Bicategory.whisker_exchange]

def homPostFromIdentity {X Y : SSet.{u}} (T : X ⟶ X) (R : X ⟶ Y)
    (α : FunctorHom (𝟙 X) T) : FunctorHom R (T ≫ R) := by
  change FunctorHom (𝟙 X ≫ R) (T ≫ R)
  exact homPost R α

def homPreFromIdentity {A X : SSet.{u}} (T : A ⟶ X) (R : X ⟶ X)
    (η : FunctorHom (𝟙 X) R) : FunctorHom T (T ≫ R) := by
  change FunctorHom (T ≫ 𝟙 X) (T ≫ R)
  exact homPre T η

lemma homPost_identity {A X : SSet.{u}} [Quasicategory X] {F G : A ⟶ X}
    (α : FunctorHom F G) : homPost (𝟙 X) α = α := by
  rw [← functorHomHomotopy_hom α]
  unfold homPost
  rw [← functorHomotopyPostcomp_hom]
  congr 1

lemma homPre_identity {A X : SSet.{u}} [Quasicategory X] {F G : A ⟶ X}
    (α : FunctorHom F G) : homPre (𝟙 A) α = α := by
  rw [← functorHomHomotopy_hom α]
  unfold homPre
  rw [← functorHomotopyPrecomp_hom]
  congr 1

lemma identityHom_exchange {X : SSet.{u}} [Quasicategory X]
    (T R : X ⟶ X) (α : FunctorHom (𝟙 X) T) (η : FunctorHom (𝟙 X) R) :
    α ≫ homPreFromIdentity T R η = η ≫ homPostFromIdentity T R α := by
  have h := homPost_homPre_exchange α η
  rw [homPost_identity, homPre_identity] at h
  exact h

def homPostFromIdentityComp {X Y Z : SSet.{u}} (T : X ⟶ X) (F : X ⟶ Y) (G : Y ⟶ Z)
    (α : FunctorHom (𝟙 X) T) : FunctorHom (F ≫ G) ((T ≫ F) ≫ G) := by
  change FunctorHom (𝟙 X ≫ (F ≫ G)) (T ≫ (F ≫ G))
  exact homPost (F ≫ G) α

def homPreFromIdentityComp {X Y : SSet.{u}} (T : X ⟶ X) (F : X ⟶ Y) (G : Y ⟶ X)
    (η : FunctorHom (𝟙 X) (F ≫ G)) : FunctorHom T ((T ≫ F) ≫ G) := by
  change FunctorHom (T ≫ 𝟙 X) (T ≫ (F ≫ G))
  exact homPre T η

lemma identityHom_exchange_comp {X Y : SSet.{u}} [Quasicategory X]
    (T : X ⟶ X) (F : X ⟶ Y) (G : Y ⟶ X)
    (α : FunctorHom (𝟙 X) T) (η : FunctorHom (𝟙 X) (F ≫ G)) :
    α ≫ homPreFromIdentityComp T F G η = η ≫ homPostFromIdentityComp T F G α :=
  identityHom_exchange T (F ≫ G) α η

end SerrePositivity.KST.LocalizingInvariants
