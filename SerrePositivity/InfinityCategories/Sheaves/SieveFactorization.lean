module

public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
概要：二つの篩の交叉に属する射を二段に分解する圏。
方針：Over U の充満部分圏の comma を使い、恒等分解と合成の随伴を作る。
使われ方：HTT 6.2.2.6 の被覆生成の降下を、反変な極限の形状比較へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 篩の交叉の射を、第一の篩の射への射として分解する圏。
元は W → V → U で、V → U は R、合成は R ⊓ S に属する。 -/
def sieveFactorizationCategory (R S : Sieve U) : Type u :=
  Comma (ObjectProperty.ι (fun f : Over U => (R ⊓ S).arrows f.hom))
    (ObjectProperty.ι (fun f : Over U => R.arrows f.hom))

instance (R S : Sieve U) : SmallCategory (sieveFactorizationCategory R S) := by
  unfold sieveFactorizationCategory
  infer_instance

/-- 分解から元の合成射を回収する。 -/
def sieveFactorizationComposite (R S : Sieve U) :
    sieveFactorizationCategory R S ⥤ sieveCategory (R ⊓ S) :=
  Comma.fst _ _

/-- 恒等分解。元の合成射をそのまま第一の篩の射として使う。 -/
def sieveFactorizationSection (R S : Sieve U) :
    sieveCategory (R ⊓ S) ⥤ sieveFactorizationCategory R S where
  obj A :=
    { left := A
      right := ⟨A.obj, A.property.1⟩
      hom := 𝟙 A.obj }
  map f :=
    { left := f
      right := ObjectProperty.homMk f.hom
      w := by simp }

/-- 恒等分解の後で合成すれば元の射と全射を厳密に回収する。 -/
lemma sieveFactorizationSection_composite (R S : Sieve U) :
    sieveFactorizationSection R S ⋙ sieveFactorizationComposite R S = 𝟭 _ := rfl

/-- 恒等分解から任意の分解への射は、合成射への射で一意に指定される。 -/
def sieveFactorizationHomEquiv (R S : Sieve U)
    (A : sieveCategory (R ⊓ S)) (B : sieveFactorizationCategory R S) :
    ((sieveFactorizationSection R S).obj A ⟶ B) ≃
      (A ⟶ (sieveFactorizationComposite R S).obj B) where
  toFun f := f.left
  invFun f :=
    { left := f
      right := ObjectProperty.homMk (f.hom ≫ B.hom)
      w := by simp [sieveFactorizationSection] }
  left_inv f := by
    apply Comma.hom_ext
    · rfl
    · apply ObjectProperty.hom_ext
      simpa [sieveFactorizationSection] using f.w
  right_inv f := rfl

/-- 恒等分解は合成の左随伴。
反変図式では合成の opposite が initial な形状比較を与えるための随伴である。 -/
def sieveFactorizationAdjunction (R S : Sieve U) :
    sieveFactorizationSection R S ⊣ sieveFactorizationComposite R S :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sieveFactorizationHomEquiv R S
      homEquiv_naturality_left_symm := by
        intro A A' B f g
        apply Comma.hom_ext
        · rfl
        · apply ObjectProperty.hom_ext
          exact Category.assoc _ _ _
      homEquiv_naturality_right := by intros; rfl }

end SerrePositivity.InfinityCategories.Sheaves
