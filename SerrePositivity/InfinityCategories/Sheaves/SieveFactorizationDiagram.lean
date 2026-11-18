module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationFiber
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：二段分解の全図式と元の篩錐の指定比較。
方針：Over の可換三角形を自然変換として保持し、fiber 上では引き戻し篩の図式を回収する。
  文献対応：HTT 6.2.2.6 の降下の合成。頂点と脚を指定したまま比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 二段分解の中間射への射影。 -/
def sieveFactorizationOuter (R S : Sieve U) :
    sieveFactorizationCategory R S ⥤ sieveCategory R := Comma.snd _ _

/-- 二段分解上の反変図式は、合成射の始域を取る。 -/
def sieveFactorizationDiagram (R S : Sieve U) :
    (sieveFactorizationCategory R S)ᵒᵖ ⥤ Cᵒᵖ :=
  (sieveFactorizationComposite R S).op ⋙ sieveDiagram (R ⊓ S)

/-- 交叉の元の錐を、二段分解の全圏へ制限した指定錐。 -/
def sieveFactorizationCone (R S : Sieve U) : Cone (sieveFactorizationDiagram R S) :=
  (sieveCone (R ⊓ S)).whisker (sieveFactorizationComposite R S).op

/-- 中間射から合成射の始域への反変な第一の脚。 -/
def sieveFactorizationTriangle (R S : Sieve U) :
    (sieveFactorizationOuter R S).op ⋙ sieveDiagram R ⟶ sieveFactorizationDiagram R S where
  app B := B.unop.hom.left.op
  naturality X Y f := by
    change (f.unop.right.hom.left).op ≫ _ = _ ≫ (f.unop.left.hom.left).op
    rw [← CategoryTheory.op_comp, ← CategoryTheory.op_comp]
    exact congrArg Quiver.Hom.op (congrArg (fun z => z.left) f.unop.w).symm

/-- 元の R の錐と三角形の合成は、元の交叉の錐の制限に等しい。 -/
lemma sieveFactorizationCone_triangle (R S : Sieve U) :
    (sieveFactorizationCone R S).π =
      Functor.whiskerLeft (sieveFactorizationOuter R S).op (sieveCone R).π ≫
        sieveFactorizationTriangle R S := by
  apply NatTrans.ext
  funext B
  change B.unop.left.obj.hom.op = B.unop.right.obj.hom.op ≫ B.unop.hom.left.op
  rw [← CategoryTheory.op_comp]
  have hw := Over.w B.unop.hom
  change B.unop.hom.left ≫ B.unop.right.obj.hom = B.unop.left.obj.hom at hw
  exact congrArg Quiver.Hom.op hw.symm

/-- 固定した中間射の fiber を全分解圏へ含める。 -/
def sieveFactorizationFiberInclusion (R S : Sieve U) (t : sieveCategory R) :
    sieveFactorizationFiber R S t ⥤ sieveFactorizationCategory R S where
  obj B := { left := B.left, right := t, hom := B.hom }
  map {B B'} f :=
    { left := f.left
      right := 𝟙 t
      w := by
        change f.left.hom ≫ B'.hom = B.hom ≫ 𝟙 t.obj
        rw [Category.comp_id]
        exact CostructuredArrow.w f }
  map_id A := by apply Comma.hom_ext <;> rfl
  map_comp f g := by
    apply Comma.hom_ext
    · rfl
    · change 𝟙 t = 𝟙 t ≫ 𝟙 t
      simp

/-- fiber 比較の下で、始域の元の全図式は厳密に一致する。 -/
lemma pullbackSieveFactorizationFiber_diagram (R S : Sieve U) (t : sieveCategory R) :
    (pullbackSieveToFactorizationFiber R S t).op ⋙
      (sieveFactorizationFiberInclusion R S t).op ⋙ sieveFactorizationDiagram R S =
        sieveDiagram (S.pullback t.obj.hom) := rfl

end SerrePositivity.InfinityCategories.Sheaves
