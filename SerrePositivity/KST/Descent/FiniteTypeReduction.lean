module

public import SerrePositivity.KST.Descent.NoetherianReduction

/-!
# 有限型スキームの圏内の被約化

## 概要
被約化の関手と包含の自然変換を、前層 L の定義域である有限型の圏内に構成する。

## 方針
構造射は被約化の包含と元の構造射の合成とする。
射の基底との両立を包含の自然性から証明する。

## 規約
この圏内の自己同型の作用を用い、スキーム上の作用との型の不一致を避ける。
構成自体は基底の Noether 性を要求しない。

## 使われ方
論文 定理 3.1 の一般から被約への還元と、公理 (3) の全次数比較。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}}

/-- 概要：有限型対象の被約化（論文 §3）。
方針：全体を台とする被約閉中心を使う。
規約：基底 S 上の有限型対象として保持する。
使われ方：前層 L が評価する reduction。 -/
noncomputable abbrev finiteTypeReduction (X : FiniteTypeSchemes S) : FiniteTypeSchemes S :=
  reducedClosedAsFiniteType X ⊤

/-- 概要：有限型の圏内の reduction の包含（論文 §3）。
方針：全体の被約閉中心の包含を使う。
規約：基底の構造射との両立を保持する。
使われ方：冪零不変性を適用する指定射。 -/
noncomputable abbrev finiteTypeReductionInclusion (X : FiniteTypeSchemes S) :
    finiteTypeReduction X ⟶ X :=
  reducedClosedAsFiniteTypeInclusion X ⊤

/-- 概要：有限型の圏内で射に誘導される reduction の射（論文 §3）。
方針：スキームの被約化の誘導射を、包含の自然性で基底上の射にする。
規約：元の射と同じ基底 S 上の射。
使われ方：降下比較の被約化との可換式。 -/
noncomputable def finiteTypeReductionMap {X Y : FiniteTypeSchemes S} (f : X ⟶ Y) :
    finiteTypeReduction X ⟶ finiteTypeReduction Y :=
  ObjectProperty.homMk (Over.homMk (schemeReductionMap f.hom.left) (by
    change schemeReductionMap f.hom.left ≫
      (schemeReductionInclusion Y.obj.left ≫ Y.obj.hom) =
      schemeReductionInclusion X.obj.left ≫ X.obj.hom
    rw [← Category.assoc, schemeReductionMap_comp_inclusion, Category.assoc, f.hom.w]))

/-- 概要：有限型の圏での包含と被約化の射の自然性（論文 §3）。
方針：スキームの射の自然性に忘却する。
規約：同じ有限型の圏内の等式。
使われ方：前層 L の反変合成による比較の可換性。 -/
@[reassoc (attr := simp)] theorem finiteTypeReductionMap_comp_inclusion
    {X Y : FiniteTypeSchemes S} (f : X ⟶ Y) :
    finiteTypeReductionMap f ≫ finiteTypeReductionInclusion Y =
      finiteTypeReductionInclusion X ≫ f := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact schemeReductionMap_comp_inclusion f.hom.left

/-- 概要：基底上有限型の圏での reduction 関手（論文 §3）。
方針：包含の mono 性で関手の法則を検査する。
規約：導来値域や π_n の関手とは別の幾何学的な関手。
使われ方：前層の定義域を保った被約化と G 作用。 -/
noncomputable def finiteTypeReductionFunctor (S : Scheme.{u}) :
    FiniteTypeSchemes S ⥤ FiniteTypeSchemes S where
  obj := finiteTypeReduction
  map := finiteTypeReductionMap
  map_id X := by
    apply ObjectProperty.hom_ext
    apply (Over.forget S).map_injective
    exact schemeReductionFunctor.map_id X.obj.left
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply (Over.forget S).map_injective
    exact schemeReductionFunctor.map_comp f.hom.left g.hom.left

/-- 概要：有限型の圏内の reduction の包含の自然変換（論文 §3）。
方針：包含の指定可換式を自然性に使う。
規約：前層を適用できる圏内の自然変換。
使われ方：被約化前後の全次数比較。 -/
noncomputable def finiteTypeReductionInclusionNat (S : Scheme.{u}) :
    finiteTypeReductionFunctor S ⟶ 𝟭 (FiniteTypeSchemes S) where
  app := finiteTypeReductionInclusion
  naturality _ _ f := finiteTypeReductionMap_comp_inclusion f

/-- 概要：有限型の圏内の G 作用を reduction へ移す（論文 定理 3.1）。
方針：reduction 関手による自己同型群の準同型と合成する。
規約：G の有限性や基底の Noether 性は構成に不要。
使われ方：前層 L の reduction 上の不変部分。 -/
noncomputable def finiteTypeReductionAction {G : Type*} [Group G]
    {X : FiniteTypeSchemes S} (action : G →* Aut X) : G →* Aut (finiteTypeReduction X) :=
  (Functor.mapAut X (finiteTypeReductionFunctor S)).comp action

/-- 概要：有限型の圏内で reduction の包含は G 同変（論文 定理 3.1）。
方針：包含の自然性を自己同型に適用する。
規約：前層 L の定義域の射の等式。
使われ方：公理 (3) の比較を不変部分へ制限する。 -/
@[reassoc] theorem finiteTypeReductionAction_comp_inclusion {G : Type*} [Group G]
    {X : FiniteTypeSchemes S} (action : G →* Aut X) (g : G) :
    (finiteTypeReductionAction action g).asIso.hom ≫ finiteTypeReductionInclusion X =
      finiteTypeReductionInclusion X ≫ (action g).asIso.hom :=
  finiteTypeReductionMap_comp_inclusion _

/-- 概要：被約な始域からの射を有限型の圏内で reduction へ持ち上げる（定理 3.1）。
方針：スキームの持ち上げと包含の合成公式で基底上の条件を検査する。
規約：始域は被約だが Noether 性は不要。
使われ方：被約な基底上の切断を非被約な始域の被約化へ移す。 -/
noncomputable def finiteTypeReductionLift {X Y : FiniteTypeSchemes S}
    [IsReduced X.obj.left] (f : X ⟶ Y) : X ⟶ finiteTypeReduction Y :=
  ObjectProperty.homMk (Over.homMk (schemeReductionLift f.hom.left) (by
    change schemeReductionLift f.hom.left ≫
      (schemeReductionInclusion Y.obj.left ≫ Y.obj.hom) = X.obj.hom
    rw [← Category.assoc, schemeReductionLift_comp_inclusion, f.hom.w]))

/-- 概要：有限型の圏内の被約化への持ち上げは指定射を因子分解する（定理 3.1）。
方針：忘却してスキームの持ち上げの合成公式を適用する。
規約：基底上の射の等式として保持する。
使われ方：被約化した始域への切断の恒等式。 -/
@[reassoc (attr := simp)] theorem finiteTypeReductionLift_comp_inclusion
    {X Y : FiniteTypeSchemes S} [IsReduced X.obj.left] (f : X ⟶ Y) :
    finiteTypeReductionLift f ≫ finiteTypeReductionInclusion Y = f := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact schemeReductionLift_comp_inclusion f.hom.left

end SerrePositivity.KST.Descent
