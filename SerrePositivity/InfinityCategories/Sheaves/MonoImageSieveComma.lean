module

public import SerrePositivity.InfinityCategories.Sheaves.SetLocalEquivalence
public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
概要：集合値単射の元の圏の局所 comma 図式を、同じ元の像篩の圏で表示する。
方針：既存の StructuredArrow と imageSieve の射をそのまま読み替える。
規約：HTT 6.2.2.6 の被覆篩による局所性への通常圏での入力。
使われ方：S8 の局所同値による切断の不変性。生の射と係数への射影を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 根を備えた局所表示を、その同じ基底射の属する像篩へ送る。 -/
def imageSieveCommaFunctor (φ : P ⟶ Q) (q : Q.Elements) :
    StructuredArrow q φ.mapElements ⥤
      (sieveCategory (CategoryTheory.Presheaf.imageSieve φ q.val))ᵒᵖ where
  obj a := Opposite.op ⟨Over.mk a.hom.hom.unop, ⟨a.right.val, a.hom.map_val.symm⟩⟩
  map {a b} f :=
    (ObjectProperty.homMk (Over.homMk f.right.hom.unop (by
      have h := congrArg (fun k => k.hom.unop) (StructuredArrow.w f)
      exact h))).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

/-- 比較関手は元の係数への射影を全射で保持する。 -/
lemma imageSieveCommaFunctor_projection (φ : P ⟶ Q) (q : Q.Elements) :
    imageSieveCommaFunctor φ q ⋙
      sieveDiagram (CategoryTheory.Presheaf.imageSieve φ q.val) =
    StructuredArrow.proj q φ.mapElements ⋙ Functor.Elements.π P := rfl

end SerrePositivity.InfinityCategories.Sheaves
