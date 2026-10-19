module

public import SerrePositivity.KST.Spectra.FreePointedHomRestriction
public import SerrePositivity.KST.Spectra.PointedExchangeVertices

/-!
概要：自由基点を除いた Hom の制限と、点つき uncurry の評価の一致。
方針：内部 Hom の源制限の評価式と、smash 商での uncurry の式を合成する。
規約：全てのパラメータでの通常の単体集合の射。使われ方：weighted end の作用の忘却。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.FreePointedHomRestriction

/-- 自由基点を除いた内部 Hom の評価は、元の成分の包含と smash 商で計算される。 -/
@[reassoc]
lemma uncurry_restrict (W : SSet.{u}) {P Y : PointedSimplicialSet.{u}}
    (q : P ⟶ PointedObject.basedHom (PointedObject.adjoin W) Y) :
    uncurry (q.right ≫ restrict W Y) =
      (coprod.inl : W ⟶ (PointedObject.adjoin W).right) ▷ P.right ≫
        PointedSimplicialSet.productToSmash (PointedObject.adjoin W) P ≫ (uncurry q).right := by
  rw [FreePointedHomRestriction.restrict, ← Category.assoc, uncurry_pre_app,
    ← PointedMapping.uncurry_quotient]
  rfl

/-- 元の内部 Hom の評価は、自由基点の包含・smash 商・点つき評価の合成。 -/
lemma restrict_evaluation (W : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    uncurry (restrict W Y) =
      (coprod.inl : W ⟶ (PointedObject.adjoin W).right) ▷
          (PointedObject.basedHom (PointedObject.adjoin W) Y).right ≫
        PointedSimplicialSet.productToSmash (PointedObject.adjoin W)
          (PointedObject.basedHom (PointedObject.adjoin W) Y) ≫
          ((ihom.ev (PointedObject.adjoin W)).app Y).right := by
  have h := uncurry_restrict W (𝟙 (PointedObject.basedHom (PointedObject.adjoin W) Y))
  have he : uncurry (𝟙 (PointedObject.basedHom (PointedObject.adjoin W) Y)) =
      (ihom.ev (PointedObject.adjoin W)).app Y :=
    uncurry_id_eq_ev (PointedObject.adjoin W) Y
  rw [he] at h
  simpa only [Under.id_right, Category.id_comp] using h

end SerrePositivity.KST.Spectra.FreePointedHomRestriction
