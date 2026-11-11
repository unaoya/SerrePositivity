module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoproductFrames
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# 余積 frame からの Hom の指定積分解

概要：HA 3.2.4.7 の検査に使う、二包含による全単体の積比較。
方針：次数評価による余積比較の同型と通常の余積の普遍性を使う。
規約：余単体的 frame と終域を変えず、二つの射影を指定する。
使われ方：native な二項余積の写像空間。［一般∞］の移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity
open CategoryTheory Limits Opposite
open SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
  (B D : SimplexCategory ⥤ C) (Z : C)

/-- 二つの指定包含による frame Hom の積比較。 -/
def coproductFrameHomRestriction : (cosimplicialHom (B ⨿ D)).obj Z ⟶
    (cosimplicialHom B).obj Z ⨯ (cosimplicialHom D).obj Z :=
  prod.lift ((cosimplicialHomMap coprod.inl).app Z)
    ((cosimplicialHomMap coprod.inr).app Z)

/-- Hom の積比較は各次数での厳密な同型。 -/
instance coproductFrameHomRestriction_isIso : IsIso (coproductFrameHomRestriction B D Z) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro n
  let E := (evaluation SimplexCategory C).obj n.unop
  let H := (evaluation SimplexCategoryᵒᵖ (Type v)).obj n
  let P := prodComparison H ((cosimplicialHom B).obj Z) ((cosimplicialHom D).obj Z) ≫
    (Types.binaryProductIso (B.obj n.unop ⟶ Z) (D.obj n.unop ⟶ Z)).hom
  have : IsIso P := by dsimp [P]; infer_instance
  suffices IsIso ((coproductFrameHomRestriction B D Z).app n ≫ P) from
    (isIso_comp_right_iff _ P).mp this
  apply (isIso_iff_bijective _).mpr
  have he : (coproductFrameHomRestriction B D Z).app n ≫ P =
      ↾(fun f : (B ⨿ D).obj n.unop ⟶ Z =>
        ((coprod.inl : B ⟶ B ⨿ D).app n.unop ≫ f,
          (coprod.inr : D ⟶ B ⨿ D).app n.unop ≫ f)) := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Prod.ext
    · have h : ((coproductFrameHomRestriction B D Z).app n ≫ P) ≫ ↾Prod.fst =
          ((cosimplicialHomMap (coprod.inl : B ⟶ B ⨿ D)).app Z).app n := by
        simp only [P, Category.assoc, Types.binaryProductIso_hom_comp_fst]
        calc
          _ = (coproductFrameHomRestriction B D Z).app n ≫ H.map prod.fst :=
            congrArg (fun k => (coproductFrameHomRestriction B D Z).app n ≫ k)
              (prodComparison_fst H ((cosimplicialHom B).obj Z) ((cosimplicialHom D).obj Z))
          _ = _ := by
            change (coproductFrameHomRestriction B D Z ≫ prod.fst).app n = _
            rw [coproductFrameHomRestriction, prod.lift_fst]
      exact congrArg (fun k => k f) h
    · have h : ((coproductFrameHomRestriction B D Z).app n ≫ P) ≫ ↾Prod.snd =
          ((cosimplicialHomMap (coprod.inr : D ⟶ B ⨿ D)).app Z).app n := by
        simp only [P, Category.assoc, Types.binaryProductIso_hom_comp_snd]
        calc
          _ = (coproductFrameHomRestriction B D Z).app n ≫ H.map prod.snd :=
            congrArg (fun k => (coproductFrameHomRestriction B D Z).app n ≫ k)
              (prodComparison_snd H ((cosimplicialHom B).obj Z) ((cosimplicialHom D).obj Z))
          _ = _ := by
            change (coproductFrameHomRestriction B D Z ≫ prod.snd).app n = _
            rw [coproductFrameHomRestriction, prod.lift_snd]
      exact congrArg (fun k => k f) h
  rw [he]
  change Function.Bijective (fun f : (B ⨿ D).obj n.unop ⟶ Z =>
    ((coprod.inl : B ⟶ B ⨿ D).app n.unop ≫ f, (coprod.inr : D ⟶ B ⨿ D).app n.unop ≫ f))
  constructor
  · intro f g h
    apply (cancel_epi (coprodComparison E B D)).mp
    apply coprod.hom_ext
    · simpa only [coprodComparison_inl_assoc, E, evaluation_obj_map] using congrArg Prod.fst h
    · simpa only [coprodComparison_inr_assoc, E, evaluation_obj_map] using congrArg Prod.snd h
  · rintro ⟨f, g⟩
    refine ⟨inv (coprodComparison E B D) ≫ coprod.desc f g, ?_⟩
    apply Prod.ext
    · change E.map coprod.inl ≫ inv (coprodComparison E B D) ≫ coprod.desc f g = f
      rw [← Category.assoc, map_inl_inv_coprodComparison, coprod.inl_desc]
    · change E.map coprod.inr ≫ inv (coprodComparison E B D) ≫ coprod.desc f g = g
      rw [← Category.assoc, map_inr_inv_coprodComparison, coprod.inr_desc]

/-- 指定された積分解の同型。 -/
def coproductFrameHomIso : (cosimplicialHom (B ⨿ D)).obj Z ≅
    (cosimplicialHom B).obj Z ⨯ (cosimplicialHom D).obj Z :=
  asIso (coproductFrameHomRestriction B D Z)

end SerrePositivity.EInfinity
