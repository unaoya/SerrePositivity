module

public import SerrePositivity.InfinityCategories.Sheaves.MonoImageSieveComma

/-!
概要：単射の根を備えた局所表示と、同じ元の像篩の圏は同値。
方針：既存の比較の忠実性・充満性・本質的全射性を通常の圏同値へ渡す。
規約：HTT 6.2.2.6 の篩による局所性に対する通常圏の表示の法則。
使われ方：S8 の局所単射の切断を、元の層条件の全錐で検出する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 局所表示の比較は元の基底射を忠実に保持する。 -/
instance imageSieveCommaFunctor_faithful (φ : P ⟶ Q) (q : Q.Elements) :
    (imageSieveCommaFunctor φ q).Faithful where
  map_injective := by
    intro a b f g h
    apply StructuredArrow.hom_ext
    apply Functor.Elements.Hom.ext
    exact congrArg (fun k => k.unop.hom.left.op) h

/-- 単射の場合、像篩の三角形から元の根の射を一意に読み戻す。 -/
instance imageSieveCommaFunctor_full (φ : P ⟶ Q) [Mono φ] (q : Q.Elements) :
    (imageSieveCommaFunctor φ q).Full where
  map_surjective {a b} f := by
    let k := f.unop.hom.left.op
    have hw : a.hom.hom ≫ k = b.hom.hom :=
      congrArg Quiver.Hom.op (Over.w f.unop.hom)
    have hp : P.map k a.right.val = b.right.val := by
      apply (CategoryTheory.mono_iff_injective (φ.app b.right.obj)).mp inferInstance
      calc
        φ.app _ (P.map k a.right.val) = Q.map k (φ.app _ a.right.val) :=
          φ.naturality_apply k a.right.val
        _ = Q.map k (Q.map a.hom.hom q.val) := by
          rw [a.hom.map_val]
          rfl
        _ = Q.map (a.hom.hom ≫ k) q.val := by rw [Q.map_comp]; rfl
        _ = φ.app _ b.right.val := by
          rw [hw]
          exact b.hom.map_val
    let g : a ⟶ b := StructuredArrow.homMk
      (⟨k, hp⟩ : a.right ⟶ b.right) (by
        apply Functor.Elements.Hom.ext
        exact hw)
    refine ⟨g, ?_⟩
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

/-- 像篩の元はその定義の根を持ち、同じ基底射の局所表示から来る。 -/
instance imageSieveCommaFunctor_essSurj (φ : P ⟶ Q) (q : Q.Elements) :
    (imageSieveCommaFunctor φ q).EssSurj where
  mem_essImage a := by
    obtain ⟨p, hp⟩ := a.unop.property
    let x : P.Elements := ⟨p⟩
    let s : q ⟶ φ.mapElements.obj x := ⟨a.unop.obj.hom.op, hp.symm⟩
    let b : StructuredArrow q φ.mapElements := StructuredArrow.mk s
    let i : ((imageSieveCommaFunctor φ q).obj b).unop.obj ≅ a.unop.obj :=
      Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ a.unop.obj.hom = a.unop.obj.hom
        exact Category.id_comp _)
    exact ⟨b, ⟨(ObjectProperty.isoMk _ i).symm.op⟩⟩

/-- 単射の局所 comma 圏は、同じ元の像篩の圏の反対と同値。
係数への元の射影は次の等式で保持する。 -/
def imageSieveCommaEquivalence (φ : P ⟶ Q) [Mono φ] (q : Q.Elements) :
    StructuredArrow q φ.mapElements ≌
      (sieveCategory (CategoryTheory.Presheaf.imageSieve φ q.val))ᵒᵖ := by
  letI : (imageSieveCommaFunctor φ q).IsEquivalence := {}
  exact (imageSieveCommaFunctor φ q).asEquivalence

/-- 同値での読み替えは、係数への元の射影を全射で保持する。 -/
lemma imageSieveCommaEquivalence_projection (φ : P ⟶ Q) [Mono φ] (q : Q.Elements) :
    (imageSieveCommaEquivalence φ q).functor ⋙
      sieveDiagram (CategoryTheory.Presheaf.imageSieve φ q.val) =
    StructuredArrow.proj q φ.mapElements ⋙ Functor.Elements.π P := rfl

end SerrePositivity.InfinityCategories.Sheaves
