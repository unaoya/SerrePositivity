module

public import SerrePositivity.KST.Spectra.PointedFactorization

/-!
# 点つき小対象分解の通常の全関手

BF 1978 §2 の逐次単射置換に使う一般の補助。
既存の実 SOA の中間対象と左右の射を変えず、可換正方形への作用を公開する。
［一般∞］移動候補。模型構造の追加仮定を置かない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.KST.Spectra

/-- 基点付き正方形を、同じ SOA の中間対象の射へ送る。 -/
def pointedFactorizationFunctor : Arrow PointedSimplicialSet.{u} ⥤
    PointedSimplicialSet.{u} where
  obj f := PointedFactorization.middle f.hom
  map {f g} s := Under.homMk
    (PointedFactorization.factorization.Z.map
      ((PointedSimplicialSet.forget.mapArrow).map s)) (by
    change (f.left.hom ≫ PointedFactorization.factorization.i.app
      (Arrow.mk f.hom.right)) ≫
        PointedFactorization.factorization.Z.map
          ((PointedSimplicialSet.forget.mapArrow).map s) =
      g.left.hom ≫ PointedFactorization.factorization.i.app (Arrow.mk g.hom.right)
    rw [Category.assoc, ← PointedFactorization.factorization.i.naturality,
      ← Category.assoc]
    change (f.left.hom ≫ s.left.right) ≫ _ = _
    rw [Under.w s.left]
    rfl)
  map_id f := by
    apply Under.UnderMorphism.ext
    exact (PointedSimplicialSet.forget.mapArrow ⋙
      PointedFactorization.factorization.Z).map_id f
  map_comp s t := by
    apply Under.UnderMorphism.ext
    exact (PointedSimplicialSet.forget.mapArrow ⋙
      PointedFactorization.factorization.Z).map_comp s t

/-- 中間対象の射は、同じ左因子と厳密に可換。 -/
lemma pointedFactorizationFunctor_left {f g : Arrow PointedSimplicialSet.{u}}
    (s : f ⟶ g) :
    PointedFactorization.left f.hom ≫ pointedFactorizationFunctor.map s =
      s.left ≫ PointedFactorization.left g.hom := by
  apply Under.UnderMorphism.ext
  exact (PointedFactorization.factorization.i.naturality
    ((PointedSimplicialSet.forget.mapArrow).map s)).symm

/-- 中間対象の射は、同じ右因子と厳密に可換。 -/
lemma pointedFactorizationFunctor_right {f g : Arrow PointedSimplicialSet.{u}}
    (s : f ⟶ g) :
    pointedFactorizationFunctor.map s ≫ PointedFactorization.right g.hom =
      PointedFactorization.right f.hom ≫ s.right := by
  apply Under.UnderMorphism.ext
  exact PointedFactorization.factorization.p.naturality
    ((PointedSimplicialSet.forget.mapArrow).map s)

end SerrePositivity.EInfinity.PowerOperation
