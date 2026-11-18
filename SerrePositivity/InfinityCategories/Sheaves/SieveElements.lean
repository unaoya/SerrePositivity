module

public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf

/-!
概要：篩の射の圏と前層の要素の圏を、基底への射影を保つ同値で結ぶ。
方針：同じ射をOverの対象と篩前層の要素として読み替える。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の制限錐の再添字。
規約：篩・基底を固定し、後続で元の指定制限錐を移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {𝒞 : Type u} [SmallCategory 𝒞]

/-- (V, f ∈ S) を Over U の対象と読む。射の向きは反転する。 -/
def sieveElementsToCategory {U : 𝒞} (S : Sieve U) :
    S.functor.Elements ⥤ (sieveCategory S)ᵒᵖ where
  obj x := Opposite.op ⟨Over.mk x.val.val, x.val.property⟩
  map f := (ObjectProperty.homMk
    (Over.homMk f.hom.unop (congrArg Subtype.val f.map_val))).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- S1 の篩の対象を、篩前層の元と読む逆関手。 -/
def sieveCategoryToElements {U : 𝒞} (S : Sieve U) :
    (sieveCategory S)ᵒᵖ ⥤ S.functor.Elements where
  obj x := S.functor.elementsMk (Opposite.op x.unop.obj.left)
    ⟨x.unop.obj.hom, x.unop.property⟩
  map f := Functor.Elements.homMk f.unop.hom.left.op
    (Subtype.ext (Over.w f.unop.hom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 篩の元の圏は、S1 の Over の充満部分圏の反対圏と同値。 -/
def sieveElementsEquivalence {U : 𝒞} (S : Sieve U) :
    S.functor.Elements ≌ (sieveCategory S)ᵒᵖ where
  functor := sieveElementsToCategory S
  inverse := sieveCategoryToElements S
  unitIso := NatIso.ofComponents
    (fun x => Functor.Elements.isoMk (Iso.refl x.obj) (by
      apply Subtype.ext
      change 𝟙 _ ≫ x.val.val = x.val.val
      simp))
    (by intro x y f; ext <;> simp <;> rfl)
  counitIso := NatIso.ofComponents
    (fun x => (ObjectProperty.isoMk (fun f : Over U => S.arrows f.hom)
      (Over.isoMk (Iso.refl _) (by simp))).op)
    (by
      intro x y f
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext (P := fun a : Over U => S.arrows a.hom)
      apply CostructuredArrow.hom_ext
      change 𝟙 _ ≫ f.unop.hom.left = f.unop.hom.left ≫ 𝟙 _
      simp)
  functor_unitIso_comp x := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext (P := fun a : Over U => S.arrows a.hom)
    apply CostructuredArrow.hom_ext
    change 𝟙 (Opposite.unop x.obj) ≫ 𝟙 _ = 𝟙 _
    simp

/-- 同値は基底 𝒞ᵒᵖ への射影を保つ。 -/
lemma sieveCategoryToElements_comp_π {U : 𝒞} (S : Sieve U) :
    sieveCategoryToElements S ⋙ Functor.Elements.π S.functor = sieveDiagram S := rfl


end SerrePositivity.InfinityCategories.Sheaves
