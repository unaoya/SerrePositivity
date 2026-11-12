module

public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# 元の frame からの全矢の圏と次数射影の随伴

概要：全ての A_i→Y を元の右脚・全可換正方形を持つ comma 圏に束ねる。
方針：恒等矢の包含からの Hom を同じ次数射へ厳密に戻す。
規約：添字は任意の通常圏。モデル構造・弱同値・極限の存在を仮定しない。
使われ方：source frame の全体から右 Kan の局所図式への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory
open CategoryTheory
variable {I : Type w} [Category.{z} I] {C : Type u} [Category.{v} C] (A : I ⥤ C)

abbrev Total := Comma A (𝟭 C)
abbrev degree : Total A ⥤ I := Comma.fst A (𝟭 C)
abbrev target : Total A ⥤ C := Comma.snd A (𝟭 C)

def identityInclusion : I ⥤ Total A where
  obj i := ⟨i, A.obj i, 𝟙 _⟩
  map f := { left := f, right := A.map f }

def homEquiv (i : I) (s : Total A) :
    ((identityInclusion A).obj i ⟶ s) ≃ (i ⟶ s.left) where
  toFun f := f.left
  invFun f :=
    { left := f
      right := A.map f ≫ s.hom
      w := by change _ = 𝟙 _ ≫ _; exact (Category.id_comp _).symm }
  left_inv f := by
    apply CommaMorphism.ext
    · rfl
    · simpa only [identityInclusion, Functor.id_map, Category.id_comp] using f.w
  right_inv _ := rfl

def identityDegreeAdjunction : identityInclusion A ⊣ degree A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv A
      homEquiv_naturality_left_symm := by
        intro i' i s f g
        apply CommaMorphism.ext
        · rfl
        · change A.map (f ≫ g) ≫ s.hom = A.map f ≫ A.map g ≫ s.hom
          rw [CategoryTheory.Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by intros; rfl }

lemma identityInclusion_degree : identityInclusion A ⋙ degree A = 𝟭 I := rfl
lemma identityInclusion_target : identityInclusion A ⋙ target A = A := rfl

def rightLeg : degree A ⋙ A ⟶ target A where
  app s := s.hom
  naturality {_s _t} f := f.w

def identityCounit : degree A ⋙ identityInclusion A ⟶ 𝟭 (Total A) :=
  (identityDegreeAdjunction A).counit

lemma identityCounit_left (s : Total A) : ((identityCounit A).app s).left = 𝟙 s.left := rfl
lemma identityCounit_right (s : Total A) : ((identityCounit A).app s).right = s.hom := by
  change A.map (𝟙 s.left) ≫ s.hom = s.hom
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory
