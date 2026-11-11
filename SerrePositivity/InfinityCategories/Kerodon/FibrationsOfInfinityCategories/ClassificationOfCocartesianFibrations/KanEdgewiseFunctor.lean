module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseLeftFilling
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanOppositeCoefficients

/-!
概要：Kan 複体とその反転の間の自然な edgewise 解像。
方針：Kan な edgewise subdivision を通常の関手にし、両端射影を自然変換へ束ねる。
規約：Kan 値の通常の図式の比較であり、𝒮 の極限や余極限を主張しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、直値の strict transport と反転した係数の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：Kan 複体の edgewise subdivision は Kan 複体の通常の圏の自己関手。
方針：単体集合の edgewise 関手を Kan 性の保存で制限する。
規約：射は通常の単体集合の射。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、Kan 値図式の自然な反転比較の共通始域。 -/
def kanEdgewiseFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj K := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K.obj, inferInstance⟩
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f
  map_id K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map_id K.obj
  map_comp f g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map_comp f g

/-- 概要：Kan な edgewise 解像の右射影を恒等関手への自然変換にする。
方針：右端射影の単体集合の射に関する自然性を使う。
規約：成分は元の右端射影そのもの。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元の Kan 値図式への自然な比較。 -/
def kanEdgewiseRight : kanEdgewiseFunctor.{u} ⟶ 𝟭 _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  app K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K.obj
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality f

/-- 概要：Kan な edgewise 解像の左射影を反転関手への自然変換にする。
方針：左端射影の単体集合の射に関する自然性を使う。
規約：成分の標的は元の Kan 複体の反転。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、反転した Kan 値図式への自然な比較。 -/
def kanEdgewiseLeft : kanEdgewiseFunctor.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor where
  app K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft K.obj
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality f

/-- 概要：Kan な edgewise 解像の右自然変換の各成分は全境界を持ち上げる。
方針：右端射影の trivial Kan fibration 性を適用する。
規約：成分を単体集合の射として判定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、Kan 値図式の右比較の対象ごとの同値。 -/
lemma kanEdgewiseRight_trivialKanFibration (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (kanEdgewiseRight.app K) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_trivialKanFibration K.obj

/-- 概要：Kan な edgewise 解像の左自然変換の各成分も全境界を持ち上げる。
方針：双対性から得た左端射影の trivial Kan fibration 性を適用する。
規約：成分の標的は反転した Kan 複体。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、Kan 値図式の左比較の対象ごとの同値。 -/
lemma kanEdgewiseLeft_trivialKanFibration (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (kanEdgewiseLeft.app K) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_trivialKanFibration K.obj

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
