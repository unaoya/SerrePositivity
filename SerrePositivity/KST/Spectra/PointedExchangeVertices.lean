module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSymmetry
public import SerrePositivity.KST.Spectra.PointedVertexComparison
public import SerrePositivity.KST.Spectra.LoopMappingPositiveEquiv

/-!
概要：点つき内部 Hom の交換が写像の頂点に及ぼす作用。
方針：零次パラメータ族と閉構造の単位による頂点の一致を使う。
規約：Kan 性を要求しない厳密な等式。
使われ方：Goerss–Jardine VIII §1。loop 交換の入力代表の比較。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 単位からの射の通常の成分は点つき後合成と可換。 -/
lemma unitUnderlyingHom_post {X Z : PointedSimplicialSet.{u}}
    (f : 𝟙_ PointedSimplicialSet.{u} ⟶ X) (g : X ⟶ Z) :
    PointedSimplicialSet.unitUnderlyingHom Z (f ≫ g) =
      PointedSimplicialSet.unitUnderlyingHom X f ≫ g.right :=
  (PointedObject.adjoinForgetAdjunction (C := SSet.{u})).homEquiv_naturality_right f g

/-- 点つき内部 Hom の二つの源を転置した実際の射。 -/
def exchangeMap {A K Y : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom K Y) : K ⟶ PointedObject.basedHom A Y :=
  curry ((β_ A K).hom ≫ uncurry f)

/-- 点つき uncurry の smash 商での評価は通常の uncurry。 -/
lemma uncurry_quotient {A K Y : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom K Y) :
    (PointedObject.smashQuotient K A).right ≫ (uncurry f).right =
      uncurry (f.right ≫ PointedObject.basedHomι K Y) := by
  have h := congrArg (fun g : A ⟶ PointedObject.basedHom K Y ↦
    g.right ≫ PointedObject.basedHomι K Y) (curry_uncurry f)
  rw [curry_eq_smashCurry, PointedObject.smashCurry_ι] at h
  have hh := congrArg (fun g ↦ MonoidalClosed.uncurry g) h
  rw [uncurry_curry] at hh
  exact hh

/-- 射の転置を通常の指数へ含めると、積の二因子の交換による転置。 -/
lemma exchangeMap_ι {A K Y : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom K Y) :
    (exchangeMap f).right ≫ PointedObject.basedHomι A Y =
      curry ((β_ A.right K.right).hom ≫
        uncurry (f.right ≫ PointedObject.basedHomι K Y)) := by
  rw [exchangeMap, curry_eq_smashCurry, PointedObject.smashCurry_ι]
  apply congrArg curry
  change (PointedObject.smashQuotient A K).right ≫
    ((β_ A K).hom.right ≫ (uncurry f).right) = _
  rw [← Category.assoc, ← Under.comp_right]
  erw [PointedObject.smashQuotient_swap]
  change (β_ A.right K.right).hom ≫
    (PointedObject.smashQuotient K A).right ≫ (uncurry f).right = _
  exact congrArg (fun g ↦ (β_ A.right K.right).hom ≫ g) (uncurry_quotient f)

/-- パラメータ族の頂点への交換同型の作用は射の転置で計算される。 -/
lemma exchange_familyVertex {A K Y : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom K Y) :
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Y).hom.right.app _ (familyVertex f) =
      familyVertex (exchangeMap f) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Y).hom.right.app _ (yonedaEquiv (pointFamily f)) =
    yonedaEquiv (pointFamily (exchangeMap f))
  erw [← yonedaEquiv_comp]
  apply congrArg yonedaEquiv
  rw [pointFamily_closed, pointFamily_closed, Category.assoc]
  have hc := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices.curry'_hom f
  have hn := unitUnderlyingHom_post
    (X := (ihom A).obj ((ihom K).obj Y)) (Z := (ihom K).obj ((ihom A).obj Y))
    (curry' f) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Y).hom
  exact congrArg (fun g ↦ PointedSimplicialSet.deltaZeroUnitIso.hom ≫ g)
    (hn.symm.trans (congrArg (PointedSimplicialSet.unitUnderlyingHom _) hc))

/-- 逆向きの loop 交換は loop 値の射を円からの射へ転置する。 -/
lemma loopSwap_inv_familyVertex {A Y : PointedSimplicialSet.{u}}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) :
    (loopSwap A Y).inv.right.app _ (familyVertex f) = familyVertex (exchangeMap f) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle A Y).inv.right.app _ _ = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv]
  exact exchange_familyVertex f

end
end SerrePositivity.KST.Spectra.PointedMapping
