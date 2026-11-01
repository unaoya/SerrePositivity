module

public import SerrePositivity.InfinityCategories.ModelBridge.ModelBifibrantDeformation
public import SerrePositivity.EInfinity.Hammock.RelativeEquivalenceUnitWeak

/-!
概要：同じ cofibrant・bifibrant の包含と次数零の変形は実 hammock Hom の弱同値を誘導する。
方針：元の両単位と全成分の弱同値性を相対逆の一般判定に代入する。
規約：元の関手の Hom 射自身を結論に残す。
使われ方：bifibrant 中継から cofibrant 部分圏へ戻す実写像空間の比較。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：同じ bifibrant 化の元の hammock Hom 射は弱同値。
方針：同じ二つの実単位を相対逆の判定へ渡す。
規約：cofibrant 源と標的の元の全 Hom。使われ方：同じ変形の導来 Hom 比較。 -/
lemma modelCofibrantToBifibrant_colimitMap_weak
    (X Y : (modelCofibrantRelativeCategory C).category) :
    IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap
      (modelCofibrantToBifibrantRelative r) X Y) :=
  Hammock.RelativeEquivalence.colimitMap_weak_of_units
    (modelCofibrantToBifibrantRelative r) modelBifibrantToCofibrantRelative
    (modelCofibrantBifibrantUnit r) (modelCofibrantBifibrantUnit_weak r)
    (modelBifibrantCofibrantUnit r) (modelBifibrantCofibrantUnit_weak r) X Y

include r in
/-- 概要：同じ bifibrant 包含の元の hammock Hom 射は弱同値。
方針：同じ二つの実単位を逆順に使う。
規約：元の包含の実射。使われ方：cofibrant 圏へ戻る導来 Hom 比較。 -/
lemma modelBifibrantToCofibrant_colimitMap_weak
    (X Y : (modelBifibrantRelativeCategory C).category) :
    IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap
      modelBifibrantToCofibrantRelative X Y) :=
  Hammock.RelativeEquivalence.colimitMap_weak_of_units
    modelBifibrantToCofibrantRelative (modelCofibrantToBifibrantRelative r)
    (modelBifibrantCofibrantUnit r) (modelBifibrantCofibrantUnit_weak r)
    (modelCofibrantBifibrantUnit r) (modelCofibrantBifibrantUnit_weak r) X Y

/-- 概要：同じ bifibrant 化の元の reduced Hom 射も弱同値。
方針：同じ相対逆の reduced Hom 版を使う。
規約：元の実射を保つ。使われ方：実 DK Hom との接続。 -/
lemma modelCofibrantToBifibrant_reducedMap_weak
    (X Y : (modelCofibrantRelativeCategory C).category) :
    IsWeakHomotopyEquivalence (Hammock.Relative.reducedMap
      (modelCofibrantToBifibrantRelative r) X Y) :=
  Hammock.RelativeEquivalence.reducedMap_weak_of_units
    (modelCofibrantToBifibrantRelative r) modelBifibrantToCofibrantRelative
    (modelCofibrantBifibrantUnit r) (modelCofibrantBifibrantUnit_weak r)
    (modelBifibrantCofibrantUnit r) (modelBifibrantCofibrantUnit_weak r) X Y

include r in
/-- 概要：同じ bifibrant 包含の元の reduced Hom 射も弱同値。
方針：同じ相対逆の reduced Hom 版を逆順に使う。
規約：元の包含自身。使われ方：元の cofibrant DK Hom への輸送。 -/
lemma modelBifibrantToCofibrant_reducedMap_weak
    (X Y : (modelBifibrantRelativeCategory C).category) :
    IsWeakHomotopyEquivalence (Hammock.Relative.reducedMap
      modelBifibrantToCofibrantRelative X Y) :=
  Hammock.RelativeEquivalence.reducedMap_weak_of_units
    modelBifibrantToCofibrantRelative (modelCofibrantToBifibrantRelative r)
    (modelBifibrantCofibrantUnit r) (modelBifibrantCofibrantUnit_weak r)
    (modelCofibrantBifibrantUnit r) (modelCofibrantBifibrantUnit_weak r) X Y

end SerrePositivity.EInfinity.SimplicialLocalization
