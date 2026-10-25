module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantRelative

/-!
概要：同じ right frame の単位を cofibrant・bifibrant 相対圏の全変形として公開する。
方針：元の次数零の実単位を両全部分圏と同じ宇宙へ持ち上げる。
規約：同じ全自然変換と元の弱同値成分を保持する。
使われ方：局所化の全反転関手族を bifibrant 部分圏から戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：元の cofibrant 対象から同じ bifibrant 化の包含への全自然な単位。
方針：同じ次数零の単位を全部分圏の射として束ねる。
規約：元の全成分を保つ。使われ方：cofibrant 圏側の変形。 -/
def cofibrantBifibrantUnit : 𝟭 (CofibrantObject C) ⟶
    cofibrantToBifibrant r ⋙ bifibrantToCofibrant C where
  app X := ObjectProperty.homMk ((FrameHom.rightFrameReplacementUnit r).app X.obj)
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    exact (FrameHom.rightFrameReplacementUnit r).naturality f.hom

/-- 概要：元の bifibrant 対象から同じ二重包含・変形への単位。
方針：同じ実単位を二つの性質を持つ対象の射にする。
規約：cofibrant 圏側と同じ底の射。使われ方：bifibrant 圏側の変形。 -/
def bifibrantCofibrantUnit : 𝟭 (BifibrantObject C) ⟶
    bifibrantToCofibrant C ⋙ cofibrantToBifibrant r where
  app X := ObjectProperty.homMk ((FrameHom.rightFrameReplacementUnit r).app X.obj)
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    exact (FrameHom.rightFrameReplacementUnit r).naturality f.hom

/-- 概要：同じ cofibrant 相対圏上の実変形の全単位。
方針：元の自然変換の対象と射の宇宙を揃える。
規約：全成分と全自然性を保つ。使われ方：全反転関手への前合成比較。 -/
def modelCofibrantBifibrantUnit : 𝟭 (modelCofibrantRelativeCategory C).category ⟶
    modelCofibrantToBifibrant r ⋙ modelBifibrantToCofibrant where
  app X := AsSmall.up.map ((cofibrantBifibrantUnit r).app (AsSmall.down.obj X))
  naturality X Y f := by
    apply ULift.ext
    exact (cofibrantBifibrantUnit r).naturality (AsSmall.down.map f)

/-- 概要：同じ bifibrant 相対圏上の実変形の全単位。
方針：元の自然変換を同じ宇宙へ持ち上げる。
規約：元の全自然変換を保持。使われ方：前合成比較の逆合成。 -/
def modelBifibrantCofibrantUnit : 𝟭 (modelBifibrantRelativeCategory C).category ⟶
    modelBifibrantToCofibrant ⋙ modelCofibrantToBifibrant r where
  app X := AsSmall.up.map ((bifibrantCofibrantUnit r).app (AsSmall.down.obj X))
  naturality X Y f := by
    apply ULift.ext
    exact (bifibrantCofibrantUnit r).naturality (AsSmall.down.map f)

/-- 概要：cofibrant 圏側の同じ単位の各成分は元の弱同値。
方針：同じ right frame の実単位の自明 cofibration 性を読む。
規約：元の相対圏の弱同値。使われ方：全反転関手族上での可逆性。 -/
lemma modelCofibrantBifibrantUnit_weak (X : (modelCofibrantRelativeCategory C).category) :
    (modelCofibrantRelativeCategory C).weakEquivalences
      ((modelCofibrantBifibrantUnit r).app X) :=
  (FrameHom.rightFrameReplacementUnit_trivialCofibration r
    ((modelCofibrantInclusion C).obj X)).2

/-- 概要：bifibrant 圏側の同じ単位の各成分も元の弱同値。
方針：同じ right frame の実単位を使う。
規約：同じ底の射を保つ。使われ方：前合成比較の逆合成の可逆性。 -/
lemma modelBifibrantCofibrantUnit_weak (X : (modelBifibrantRelativeCategory C).category) :
    (modelBifibrantRelativeCategory C).weakEquivalences
      ((modelBifibrantCofibrantUnit r).app X) :=
  (FrameHom.rightFrameReplacementUnit_trivialCofibration r
    ((modelBifibrantInclusion C).obj X)).2

/-- 概要：同じ実 bifibrant 化を相対関手として公開する。
方針：元の全弱同値の保存を束ねる。
規約：元の変形関手を順射に保つ。使われ方：hammock 局所化への関手化。 -/
def modelCofibrantToBifibrantRelative : LocalizerMorphism
    (modelCofibrantRelativeCategory C).weakEquivalences
    (modelBifibrantRelativeCategory C).weakEquivalences :=
  ⟨modelCofibrantToBifibrant r, fun _ _ f hf => modelCofibrantToBifibrant_map_weak r f hf⟩

/-- 概要：元の bifibrant 包含を相対関手として公開する。
方針：元の全弱同値の保存を束ねる。
規約：元の包含自身。使われ方：hammock 比較の逆側。 -/
def modelBifibrantToCofibrantRelative : LocalizerMorphism
    (modelBifibrantRelativeCategory C).weakEquivalences
    (modelCofibrantRelativeCategory C).weakEquivalences :=
  ⟨modelBifibrantToCofibrant, fun _ _ f hf => modelBifibrantToCofibrant_map_weak f hf⟩

end SerrePositivity.EInfinity.SimplicialLocalization
