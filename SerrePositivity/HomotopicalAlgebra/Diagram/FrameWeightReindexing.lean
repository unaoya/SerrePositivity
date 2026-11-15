module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightRealization

/-!
概要：既存のframe重み実現の添字変更射と、その指定随伴における転置の式。
方針：pointwise Homの制限を同定し、元の単位を制限して随伴転置する。
規約：実際の実現対象を使う。添字変更の弱同値性はこの法則からは主張しない。
使われ方：HTT 4.2.4.4のRR02(a)、指定増大射を保つ添字変更。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (P : L ⥤ K) (A : K ⥤ SimplexCategory ⥤ C)

/-- frame Homの添字変更は、元のpointwise Homの制限に一致する。 -/
def homReindexIso :
    hom K A ⋙ (Functor.whiskeringLeft Lᵒᵖ Kᵒᵖ SSet.{w}).obj P.op ≅
      hom L (P ⋙ A) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro Y Z f; rfl)

/-- 同じ実現随伴の単位を制限して得る、実現の指定添字変更射。 -/
def reindexMap (W : Kᵒᵖ ⥤ SSet.{w}) :
    (functor L (P ⋙ A)).obj (P.op ⋙ W) ⟶ (functor K A).obj W :=
  ((adjunction L (P ⋙ A)).homEquiv _ _).symm
    (Functor.whiskerLeft P.op ((adjunction K A).unit.app W) ≫
      (homReindexIso P A).hom.app ((functor K A).obj W))

/-- 添字変更射の転置は、元の指定単位を制限した射そのもの。 -/
lemma reindexMap_homEquiv (W : Kᵒᵖ ⥤ SSet.{w}) :
    (adjunction L (P ⋙ A)).homEquiv _ _ (reindexMap P A W) =
      Functor.whiskerLeft P.op ((adjunction K A).unit.app W) ≫
        (homReindexIso P A).hom.app ((functor K A).obj W) :=
  ((adjunction L (P ⋙ A)).homEquiv _ _).apply_symm_apply _

/-- 任意の標的射について、転置と添字変更の順序は一致する。 -/
lemma reindexMap_homEquiv_comp (W : Kᵒᵖ ⥤ SSet.{w}) (Y : C)
    (f : (functor K A).obj W ⟶ Y) :
    (adjunction L (P ⋙ A)).homEquiv _ Y (reindexMap P A W ≫ f) =
      Functor.whiskerLeft P.op ((adjunction K A).homEquiv W Y f) ≫
        (homReindexIso P A).hom.app Y := by
  rw [Adjunction.homEquiv_naturality_right, reindexMap_homEquiv]
  rw [Category.assoc, ← (homReindexIso P A).hom.naturality]
  rw [← Category.assoc, (adjunction K A).homEquiv_unit]
  rfl

/-- 添字変更射は全ての重みの射について自然。 -/
lemma reindexMap_naturality {W W' : Kᵒᵖ ⥤ SSet.{w}} (f : W ⟶ W') :
    (functor L (P ⋙ A)).map (Functor.whiskerLeft P.op f) ≫ reindexMap P A W' =
      reindexMap P A W ≫ (functor K A).map f := by
  apply ((adjunction L (P ⋙ A)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, reindexMap_homEquiv,
    reindexMap_homEquiv_comp, (adjunction K A).homEquiv_unit]
  change Functor.whiskerLeft P.op f ≫
      (Functor.whiskerLeft P.op ((adjunction K A).unit.app W') ≫ 𝟙 _) =
    Functor.whiskerLeft P.op
      ((adjunction K A).unit.app W ≫ (hom K A).map ((functor K A).map f)) ≫ 𝟙 _
  simp only [Category.comp_id, ← Functor.whiskerLeft_comp]
  exact congrArg (Functor.whiskerLeft P.op) ((adjunction K A).unit.naturality f)

/-- 元の実現への添字変更射を、重み全体の一つの自然変換に束ねる。 -/
def reindexTransformation :
    (Functor.whiskeringLeft Lᵒᵖ Kᵒᵖ SSet.{w}).obj P.op ⋙ functor L (P ⋙ A) ⟶
      functor K A where
  app := reindexMap P A
  naturality _ _ f := reindexMap_naturality P A f

end SerrePositivity.DiagramModel.FrameWeightRealization
