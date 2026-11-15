module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationDiagram

/-!
概要：二段分解の射影の局所 comma を、固定した中間射の fiber へ縮める。
方針：中間射から t への射を合成し、恒等射で入れる包含との随伴を明示する。
使われ方：HTT 6.2.2.6 の被覆生成。反変図式の局所右 Kan の形状比較に使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 射影から t への局所 comma。反転すると右 Kan の局所添字になる。 -/
abbrev sieveFactorizationLocalComma (R S : Sieve U) (t : sieveCategory R) :=
  CostructuredArrow (sieveFactorizationOuter R S) t

/-- 局所 comma の元を、t への合成三角形に送る。 -/
def sieveFactorizationLocalPush (R S : Sieve U) (t : sieveCategory R) :
    sieveFactorizationLocalComma R S t ⥤ sieveFactorizationFiber R S t where
  obj B := CostructuredArrow.mk (B.left.hom ≫ B.hom.hom)
  map {B B'} f := CostructuredArrow.homMk f.left.left (by
    change f.left.left.hom ≫ (B'.left.hom ≫ B'.hom.hom) = B.left.hom ≫ B.hom.hom
    have hw := f.left.w
    change f.left.left.hom ≫ B'.left.hom = B.left.hom ≫ f.left.right.hom at hw
    have ht := congrArg (fun z => z.hom) (CostructuredArrow.w f)
    change f.left.right.hom ≫ B'.hom.hom = B.hom.hom at ht
    rw [← Category.assoc, hw, Category.assoc, ht])
  map_id B := by apply CostructuredArrow.hom_ext; rfl
  map_comp f g := by apply CostructuredArrow.hom_ext; rfl

/-- 固定 fiber の元を、t の恒等射によって局所 comma へ入れる。 -/
def sieveFactorizationLocalInclusion (R S : Sieve U) (t : sieveCategory R) :
    sieveFactorizationFiber R S t ⥤ sieveFactorizationLocalComma R S t where
  obj B := CostructuredArrow.mk (Y := (sieveFactorizationFiberInclusion R S t).obj B) (𝟙 t)
  map f := CostructuredArrow.homMk ((sieveFactorizationFiberInclusion R S t).map f) (by
    change 𝟙 t ≫ 𝟙 t = 𝟙 t
    exact Category.id_comp _)
  map_id B := by
    apply CostructuredArrow.hom_ext
    exact (sieveFactorizationFiberInclusion R S t).map_id B
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact (sieveFactorizationFiberInclusion R S t).map_comp f g

/-- 合成した三角形からの射と、局所 comma での射の全単射。 -/
def sieveFactorizationLocalHomEquiv (R S : Sieve U) (t : sieveCategory R)
    (B : sieveFactorizationLocalComma R S t) (A : sieveFactorizationFiber R S t) :
    ((sieveFactorizationLocalPush R S t).obj B ⟶ A) ≃
      (B ⟶ (sieveFactorizationLocalInclusion R S t).obj A) where
  toFun f := CostructuredArrow.homMk
    { left := f.left
      right := B.hom
      w := by
        change f.left.hom ≫ A.hom = B.left.hom ≫ B.hom.hom
        exact CostructuredArrow.w f }
    (by change B.hom ≫ 𝟙 t = B.hom; exact Category.comp_id _)
  invFun f := CostructuredArrow.homMk f.left.left (by
    have hw := f.left.w
    change f.left.left.hom ≫ A.hom = B.left.hom ≫ f.left.right.hom at hw
    have ht := CostructuredArrow.w f
    change f.left.right ≫ 𝟙 t = B.hom at ht
    have ht' : f.left.right = B.hom := (Category.comp_id f.left.right).symm.trans ht
    change f.left.left.hom ≫ A.hom = B.left.hom ≫ B.hom.hom
    exact hw.trans (congrArg (fun k => B.left.hom ≫ k.hom) ht'))
  left_inv f := by apply CostructuredArrow.hom_ext; rfl
  right_inv f := by
    apply CostructuredArrow.hom_ext
    apply Comma.hom_ext
    · rfl
    · have ht := CostructuredArrow.w f
      change f.left.right ≫ 𝟙 t = B.hom at ht
      exact ((Category.comp_id f.left.right).symm.trans ht).symm

/-- 合成による押し出しは、局所 comma への fiber 包含の左随伴。
この随伴の反転で、局所極限を fiber 上で計算するための initial な比較を得る。 -/
def sieveFactorizationLocalAdjunction (R S : Sieve U) (t : sieveCategory R) :
    sieveFactorizationLocalPush R S t ⊣ sieveFactorizationLocalInclusion R S t :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sieveFactorizationLocalHomEquiv R S t
      homEquiv_naturality_left_symm := by
        intros
        apply CostructuredArrow.hom_ext
        rfl
      homEquiv_naturality_right := by
        intro B A A' f g
        apply CostructuredArrow.hom_ext
        apply Comma.hom_ext
        · rfl
        · change B.hom = B.hom ≫ 𝟙 t
          exact (Category.comp_id _).symm }

end SerrePositivity.InfinityCategories.Sheaves
