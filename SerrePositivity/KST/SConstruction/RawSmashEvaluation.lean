module
public import SerrePositivity.KST.SConstruction.RawCofiberTensorDesc

/-! # 元の通常の積上での smash と cofiber の降下の評価
概要：自由な基点と smash を経由する降下を、元の通常の積へ厳密に引き戻す。
方針：自由基点と積の比較の逆、smash 商の自然性、元の cofiber 商射の式を使う。
規約：元の通常の商を保つ。使われ方：suspension の構造射の随伴を区間上で照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory SSet

/-- 自由な基点を加えた smash の射を元の通常の積へ戻すと元の射を回収する。 -/
lemma adjoinTensorMap_first {A B : SSet.{u}} (Z : PointedSimplicialSet.{u})
    (h : A ⊗ B ⟶ Z.right) :
    ((coprod.inl ⊗ₘ coprod.inl) ≫
      (PointedObject.smashQuotient (PointedObject.adjoin A) (PointedObject.adjoin B)).right) ≫
        (adjoinTensorMap Z h).right = h := by
  rw [← PointedObject.adjoinSmashInv_first]
  have hc : PointedObject.adjoinSmashInv A B ≫ adjoinTensorMap Z h =
      (PointedObject.adjoinHomEquiv (A ⊗ B) Z).symm h := by
    rw [adjoinTensorMap, ← Category.assoc, PointedObject.adjoinSmashInv_hom,
      Category.id_comp]
  rw [Category.assoc, ← Under.comp_right, hc]
  exact (PointedObject.adjoinHomEquiv (A ⊗ B) Z).apply_symm_apply h

/-- 通常の積から自由な基点と cofiber の smash へ行く二つの商射は厳密に一致する。 -/
lemma cofiberSmashProjection_first {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D) :
    ((coprod.inl ⊗ₘ coprod.inl) ≫
      (PointedObject.smashQuotient (PointedObject.adjoin B) (PointedObject.adjoin D)).right) ≫
        (PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g).right =
      (PointedObject.cofiberQuotient f ⊗ₘ PointedObject.cofiberQuotient g) ≫
        (PointedObject.smashQuotient
          (PointedObject.cofiber f) (PointedObject.cofiber g)).right := by
  rw [Category.assoc]
  change (coprod.inl ⊗ₘ coprod.inl) ≫
    (PointedObject.smashQuotient (PointedObject.adjoin B) (PointedObject.adjoin D)).right ≫
      (PointedObject.smashMap (PointedObject.cofiberProjection f)
        (PointedObject.cofiberProjection g)).right = _
  rw [← Under.comp_right, PointedObject.smashQuotient_map, Under.comp_right,
    PointedObject.prodMap_right, ← Category.assoc, tensorHom_comp_tensorHom,
    PointedObject.cofiberProjection_underlying, PointedObject.cofiberProjection_underlying]

/-- 元の通常の二つの商射と smash の商で、二つの cofiber への降下を元の射へ戻す。 -/
lemma rawCofiberTensorDesc_evaluation {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (Z : PointedSimplicialSet.{u}) (h : B ⊗ D ⟶ Z.right) (hf hg) :
    (PointedObject.cofiberQuotient f ⊗ₘ PointedObject.cofiberQuotient g) ≫
      (PointedObject.smashQuotient (PointedObject.cofiber f) (PointedObject.cofiber g)).right ≫
        (rawCofiberTensorDesc f g Z h hf hg).right = h := by
  have he := congrArg (fun k => ((coprod.inl ⊗ₘ coprod.inl) ≫
      (PointedObject.smashQuotient
        (PointedObject.adjoin B) (PointedObject.adjoin D)).right) ≫ k.right)
    (rawCofiberTensorDesc_quotient f g Z h hf hg)
  change ((coprod.inl ⊗ₘ coprod.inl) ≫
    (PointedObject.smashQuotient (PointedObject.adjoin B) (PointedObject.adjoin D)).right) ≫
      ((PointedObject.cofiberProjection f ⊗ₘ PointedObject.cofiberProjection g).right ≫
        (rawCofiberTensorDesc f g Z h hf hg).right) = _ at he
  rw [← Category.assoc, cofiberSmashProjection_first, adjoinTensorMap_first] at he
  exact he

end SerrePositivity.KST.SConstruction
