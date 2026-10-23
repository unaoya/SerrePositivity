module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseLeftFilling
public import SerrePositivity.InfinityCategories.F1.KanModels.KanOppositeCoefficients

/-!
概要：Kan 複体とその反転の間の自然な edgewise 解像。
方針：Kan な edgewise subdivision を通常の関手にし、両端射影を自然変換へ束ねる。
規約：Kan 値の通常の図式の比較であり、𝒮 の極限や余極限を主張しない。
使われ方：Kerodon Corollary 5.6.0.6、直値の strict transport と反転した係数の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：Kan 複体の edgewise subdivision は Kan 複体の通常の圏の自己関手。
方針：単体集合の edgewise 関手を Kan 性の保存で制限する。
規約：射は通常の単体集合の射。
使われ方：Kerodon Corollary 5.6.0.6、Kan 値図式の自然な反転比較の共通始域。 -/
def kanEdgewiseFunctor : KanObject.{u} ⥤ KanObject.{u} where
  obj K := ⟨edgewiseSubdivision K.obj, inferInstance⟩
  map f := edgewiseSubdivisionMap f
  map_id K := edgewiseSubdivisionFunctor.map_id K.obj
  map_comp f g := edgewiseSubdivisionFunctor.map_comp f g

/-- 概要：Kan な edgewise 解像の右射影を恒等関手への自然変換にする。
方針：右端射影の単体集合の射に関する自然性を使う。
規約：成分は元の右端射影そのもの。
使われ方：Kerodon Corollary 5.6.0.6、元の Kan 値図式への自然な比較。 -/
def kanEdgewiseRight : kanEdgewiseFunctor.{u} ⟶ 𝟭 KanObject.{u} where
  app K := edgewiseRight K.obj
  naturality _ _ f := edgewiseRight_naturality f

/-- 概要：Kan な edgewise 解像の左射影を反転関手への自然変換にする。
方針：左端射影の単体集合の射に関する自然性を使う。
規約：成分の標的は元の Kan 複体の反転。
使われ方：Kerodon Corollary 5.6.0.6、反転した Kan 値図式への自然な比較。 -/
def kanEdgewiseLeft : kanEdgewiseFunctor.{u} ⟶ kanObjectOpFunctor where
  app K := edgewiseLeft K.obj
  naturality _ _ f := edgewiseLeft_naturality f

/-- 概要：Kan な edgewise 解像の右自然変換の各成分は全境界を持ち上げる。
方針：右端射影の trivial Kan fibration 性を適用する。
規約：成分を単体集合の射として判定する。
使われ方：Kerodon Corollary 5.6.0.6、Kan 値図式の右比較の対象ごとの同値。 -/
lemma kanEdgewiseRight_trivialKanFibration (K : KanObject.{u}) :
    TrivialKanFibration (kanEdgewiseRight.app K) :=
  edgewiseRight_trivialKanFibration K.obj

/-- 概要：Kan な edgewise 解像の左自然変換の各成分も全境界を持ち上げる。
方針：双対性から得た左端射影の trivial Kan fibration 性を適用する。
規約：成分の標的は反転した Kan 複体。
使われ方：Kerodon Corollary 5.6.0.6、Kan 値図式の左比較の対象ごとの同値。 -/
lemma kanEdgewiseLeft_trivialKanFibration (K : KanObject.{u}) :
    TrivialKanFibration (kanEdgewiseLeft.app K) :=
  edgewiseLeft_trivialKanFibration K.obj

end SerrePositivity.InfinityCategories
