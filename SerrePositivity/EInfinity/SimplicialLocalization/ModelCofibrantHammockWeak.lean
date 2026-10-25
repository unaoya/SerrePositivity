module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelCofibrantDeformation
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantHammockWeak

/-!
概要：指定第一分解の同じ cofibrant 置換は全 C の hammock Hom と弱比較する。
方針：元の両側の比較自然変換を相対逆の一般判定へ渡す。
規約：関手的第一分解はこの補助入口の明示入力に残し、主定理から隠さない。
使われ方：実 dg モデルで bifibrant 中継を全 C の Hom と比較する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
variable (C : Type u) [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]

/-- 概要：元の cofibrant 包含の全 C の hammock Hom 射は弱同値。
方針：同じ二つの実余単位を相対逆の判定へ渡す。
規約：同じ元の包含自身。使われ方：全 C の指定局所化への Hom 比較。 -/
lemma modelCofibrantToModel_colimitMap_weak
    (X Y : (modelCofibrantRelativeCategory C).category) :
    IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap (modelCofibrantToModelRelative C) X Y) :=
  Hammock.RelativeEquivalence.colimitMap_weak (modelCofibrantToModelRelative C)
    (modelToCofibrantRelative C) (cofibrantModelSmallCounit C) (cofibrantModelSmallCounit_weak C)
    (modelCofibrantCounit C) (modelCofibrantCounit_weak C) X Y

/-- 概要：同じ全 C からの cofibrant 置換の Hom 射も弱同値。
方針：同じ両余単位を逆順に使う。
規約：元の置換関手自身。使われ方：同じ Hom 比較の逆側。 -/
lemma modelToCofibrant_colimitMap_weak
    (X Y : (modelRelativeCategory C).category) :
    IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap (modelToCofibrantRelative C) X Y) :=
  Hammock.RelativeEquivalence.colimitMap_weak (modelToCofibrantRelative C)
    (modelCofibrantToModelRelative C) (modelCofibrantCounit C) (modelCofibrantCounit_weak C)
    (cofibrantModelSmallCounit C) (cofibrantModelSmallCounit_weak C) X Y

variable {C} (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：元の bifibrant 相対圏から全 C への同じ相対包含。
方針：同じ二つの元の包含を合成する。
規約：底の射は元の同じ射。使われ方：bifibrant frame と全モデルの hammock。 -/
def modelBifibrantToModelRelative : LocalizerMorphism
    (modelBifibrantRelativeCategory C).weakEquivalences
    (modelRelativeCategory C).weakEquivalences :=
  modelBifibrantToCofibrantRelative.comp (modelCofibrantToModelRelative C)

include r in
/-- 概要：元の bifibrant 包含の全モデル hammock Hom 射は弱同値。
方針：同じ二つの包含の実 Hom 比較を合成する。
規約：同じ元の相対包含自身。使われ方：元の bifibrant frame の弱比較。 -/
lemma modelBifibrantToModel_colimitMap_weak
    (X Y : (modelBifibrantRelativeCategory C).category) :
    IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap modelBifibrantToModelRelative X Y) := by
  rw [modelBifibrantToModelRelative, Hammock.Relative.colimitMap_comp]
  exact (modelBifibrantToCofibrant_colimitMap_weak r X Y).comp
    (modelCofibrantToModel_colimitMap_weak C _ _)

end SerrePositivity.EInfinity.SimplicialLocalization
