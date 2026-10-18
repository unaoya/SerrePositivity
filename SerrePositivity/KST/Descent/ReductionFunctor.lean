module

public import SerrePositivity.KST.Descent.AffineReduction

/-!
# 被約化の普遍性と関手性

## 概要
被約スキームからの射は、終域の構成済みの reduction を一意に経由する。
この普遍性から、被約化を関手にして包含の自然性を証明する。

## 方針
被約な始域では終域の nilradical の切断が零へ写るため、閉埋め込みの普遍性で持ち上げる。
一意性は閉埋め込みの mono 性による。

## 規約
Noether 性やアフィン性はこの普遍性には不要。
任意の基底変更が被約性を保つとは主張しない。

## 使われ方
論文 定理 3.1 で section の各 G 平行移動を V = (X ×_S Y)_red に因子分解し、
被約化上にも G 作用を移すための関手的な入力。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：reduction の包含は一般のスキームでも閉埋め込み（論文 §3）。
方針：消滅イデアル層による閉部分スキームの包含を使う。
規約：核の冪零性や Noether 性はこの事実には不要。
使われ方：被約な始域からの射の一意な持ち上げ。 -/
instance schemeReductionInclusion_isClosedImmersion (X : Scheme.{u}) :
    IsClosedImmersion (schemeReductionInclusion X) :=
  reducedClosedInclusion_isClosedImmersion _

/-- 概要：reduction の包含の核は元のスキームの nilradical（論文 §3）。
方針：閉部分スキームの包含の核と、全体の消滅イデアル層の公式を使う。
規約：冪零指数の存在を主張するものではない。
使われ方：射の因子分解の条件と、公理 (3) の検証。 -/
theorem schemeReductionInclusion_ker (X : Scheme.{u}) :
    (schemeReductionInclusion X).ker = X.nilradical := by
  change (Scheme.IdealSheafData.vanishingIdeal
    (⊤ : TopologicalSpace.Closeds X)).subschemeι.ker = _
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.vanishingIdeal_top]

/-- 概要：被約な始域からの射は終域の nilradical を零にする（論文 定理 3.1）。
方針：各アフィン開集合の冪零な切断の像を、始域の被約な切断環で零にする。
規約：射の準コンパクト性は不要で、核イデアル層の最大性を使う。
使われ方：section を V へ因子分解する閉埋め込みの普遍性。 -/
theorem nilradical_le_ker_of_reduced_source {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) :
    Y.nilradical ≤ f.ker := by
  apply Scheme.IdealSheafData.le_ofIdeals_iff.mpr
  intro U x hx
  change x ∈ nilradical Γ(Y, U) at hx
  change (f.app U).hom x = 0
  exact ((mem_nilradical.mp hx).map (f.app U).hom).eq_zero

/-- 概要：被約な始域からの射を終域の reduction へ持ち上げる（論文 定理 3.1）。
方針：nilradical が射の核に含まれることと、閉埋め込みの普遍性を使う。
規約：始域の被約性を明示する。
使われ方：被約な基底上の translated section の V への因子分解。 -/
noncomputable def schemeReductionLift {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) :
    X ⟶ schemeReduction Y :=
  IsClosedImmersion.lift (schemeReductionInclusion Y) f (by
    rw [schemeReductionInclusion_ker]
    exact nilradical_le_ker_of_reduced_source f)

/-- 概要：被約化への持ち上げを包含と合成すると元の射（論文 定理 3.1）。
方針：閉埋め込みの持ち上げの合成公式を使う。
規約：幾何学的な指定射との可換式を保持する。
使われ方：section と群作用の比較の自然性。 -/
@[reassoc (attr := simp)] theorem schemeReductionLift_comp_inclusion
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) :
    schemeReductionLift f ≫ schemeReductionInclusion Y = f :=
  IsClosedImmersion.lift_fac _ _ _

/-- 概要：被約化への持ち上げは一意（論文 定理 3.1）。
方針：包含の mono 性で後合成を消去する。
規約：単なる点写像ではなくスキームの射の一意性。
使われ方：被約化の関手性と、作用の法則の移行。 -/
theorem schemeReductionLift_unique {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y)
    (g : X ⟶ schemeReduction Y) (fac : g ≫ schemeReductionInclusion Y = f) :
    g = schemeReductionLift f := by
  apply (cancel_mono (schemeReductionInclusion Y)).mp
  rw [fac, schemeReductionLift_comp_inclusion]

/-- 概要：任意のスキームの射に誘導される被約化の射（論文 §3）。
方針：始域の reduction から終域への合成を、終域の reduction へ持ち上げる。
規約：元のスキームの被約性は要求しない。
使われ方：被約化上への G 作用の移行。 -/
noncomputable def schemeReductionMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeReduction X ⟶ schemeReduction Y :=
  schemeReductionLift (schemeReductionInclusion X ≫ f)

/-- 概要：被約化の射は包含と自然に可換（論文 §3）。
方針：持ち上げの合成公式を使う。
規約：同変性の後の計算で用いる指定等式。
使われ方：群作用と前層の引き戻しの両立。 -/
@[reassoc (attr := simp)] theorem schemeReductionMap_comp_inclusion
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeReductionMap f ≫ schemeReductionInclusion Y = schemeReductionInclusion X ≫ f :=
  schemeReductionLift_comp_inclusion _

/-- 概要：被約化をスキームの関手として構成（論文 §3）。
方針：誘導射の恒等射・合成保存を包含の mono 性で確認する。
規約：L9 のスペクトルや π_n の関手とは別のスキームの関手。
使われ方：V の reduction 上の G 作用と、被約化の自然な比較。 -/
noncomputable def schemeReductionFunctor : Scheme.{u} ⥤ Scheme.{u} where
  obj := schemeReduction
  map := schemeReductionMap
  map_id X := by
    apply (cancel_mono (schemeReductionInclusion X)).mp
    simp only [schemeReductionMap_comp_inclusion, Category.comp_id, Category.id_comp]
  map_comp f g := by
    apply (cancel_mono (schemeReductionInclusion _)).mp
    simp only [Category.assoc, schemeReductionMap_comp_inclusion,
      schemeReductionMap_comp_inclusion_assoc]

/-- 概要：reduction の包含の自然変換（論文 §3）。
方針：包含と誘導射の可換式を自然性とする。
規約：元のスキームの恒等関手への自然変換。
使われ方：G 同変な被約化と前層 L の比較の組み立て。 -/
noncomputable def schemeReductionInclusionNat : schemeReductionFunctor ⟶ 𝟭 Scheme.{u} where
  app := schemeReductionInclusion
  naturality _ _ f := schemeReductionMap_comp_inclusion f

/-- 概要：スキームの G 作用を被約化上へ移す（論文 定理 3.1）。
方針：被約化関手が誘導する自己同型群の準同型と合成する。
規約：有限性や Noether 性はこの作用の構成には不要。
使われ方：V = (X ×_S Y)_red の作用と、軌道正方形の構成。 -/
noncomputable def schemeReductionAction {G : Type*} [Group G] {X : Scheme.{u}}
    (action : G →* Aut X) : G →* Aut (schemeReduction X) :=
  (Functor.mapAut X schemeReductionFunctor).comp action

/-- 概要：被約化の包含は誘導された G 作用について同変（論文 定理 3.1）。
方針：被約化の射と包含の自然性を自己同型に適用する。
規約：各群元についてスキームの射の可換式を与える。
使われ方：被約化に対する前層の比較を不変部分へ制限する。 -/
@[reassoc] theorem schemeReductionAction_comp_inclusion
    {G : Type*} [Group G] {X : Scheme.{u}} (action : G →* Aut X) (g : G) :
    (schemeReductionAction action g).asIso.hom ≫ schemeReductionInclusion X =
      schemeReductionInclusion X ≫ (action g).asIso.hom :=
  schemeReductionMap_comp_inclusion _

end SerrePositivity.KST.Descent
