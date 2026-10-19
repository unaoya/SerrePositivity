module

public import SerrePositivity.InfinityCategories.F1B.KanUnitCommaFiberLeftFibration
public import SerrePositivity.InfinityCategories.F1B.UnitCommaFiberExtension
public import SerrePositivity.InfinityCategories.F1B.MappingParameters

/-!
概要：固定始域の comma の標的上の fiber を両端固定の区間写像空間と同型にする。
方針：二重の fiber の包含を展開し、指定両端で curry する。逆は定値の標的の comma の族。
規約：同型の構成に quasicategory 性は不要。
使われ方：局所 Kan 添字の比較の各 fiber を既存の写像空間比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：二重の fiber の普遍的な矢印の族を区間模型へ写す。
方針：始域と標的の定値条件で両端を認証する。
規約：G と二つの頂点は任意。
使われ方：comma の fiber の表示の順方向。 -/
def kanUnitCommaFiberToInterval {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    vertexFiber (kanUnitCommaFiberProjection G x) y ⟶
      intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) :=
  let r := vertexFiberι (kanUnitCommaFiberProjection G x) y ≫ vertexFiberι (unitCommaSource G) x
  intervalFamilyCurry (unitCommaUncurry r)
    (by
      rw [unitCommaUncurry_zero]
      dsimp only [r]
      rw [Category.assoc, vertexFiberι_comp, SSet.comp_const])
    (by
      rw [unitCommaUncurry_one]
      change (vertexFiberι (kanUnitCommaFiberProjection G x) y ≫
        kanUnitCommaFiberProjection G x) ≫ G = _
      rw [vertexFiberι_comp, SSet.const_comp])

/-- 概要：二重の fiber からの比較の展開は元の矢印の族。
方針：区間模型の curry と uncurry の往復。
規約：射として厳密な等式。
使われ方：比較が表す写像空間の射の同定。 -/
lemma kanUnitCommaFiberToInterval_uncurry {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    intervalMappingUncurry (kanUnitCommaFiberToInterval G x y) =
      unitCommaUncurry (vertexFiberι (kanUnitCommaFiberProjection G x) y ≫
        vertexFiberι (unitCommaSource G) x) := by
  unfold kanUnitCommaFiberToInterval
  exact intervalFamilyUncurry_curry _ _ _

/-- 概要：区間写像空間の普遍族を定値の標的を持つ comma のホモトピーとして読む。
方針：標的を G(y) の定値図式から定値 y の後合成へ正規化する。
規約：端点の式だけを書き換え、ホモトピーの射は保つ。
使われ方：二重の fiber の表示の逆方向の入力。 -/
def kanIntervalToUnitCommaHomotopy {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    SSet.Homotopy
      (SSet.const x : intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) ⟶ X)
      ((SSet.const y) ≫ G) where
  h := (intervalFamilyHomotopy (𝟙 (intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)))).h
  h₀ := (intervalFamilyHomotopy (𝟙 _)).h₀
  h₁ := by rw [(intervalFamilyHomotopy (𝟙 _)).h₁, SSet.const_comp]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：区間の両端固定の族を二重の comma の fiber に戻す。
方針：定値標的の comma の族を、その標的の fiber へ持ち上げる。
規約：同型性は両方向の展開で後に証明する。
使われ方：comma の fiber の表示の逆方向。 -/
def kanIntervalToUnitCommaFiber {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) ⟶
      vertexFiber (kanUnitCommaFiberProjection G x) y :=
  vertexFiberLift _ _ (unitCommaFiberCurry G x (SSet.const y)
    (kanIntervalToUnitCommaHomotopy G x y)) (unitCommaFiberCurry_target _ _ _ _)

/-- 概要：逆方向の比較を展開すると元の区間の普遍族。
方針：二重の包含の後、comma の curry の計算と二変数の交換を相殺する。
規約：任意の単体集合の射 G。
使われ方：両逆性の計算の逆方向。 -/
lemma kanIntervalToUnitCommaFiber_uncurry {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    unitCommaUncurry (kanIntervalToUnitCommaFiber G x y ≫
      vertexFiberι (kanUnitCommaFiberProjection G x) y ≫ vertexFiberι (unitCommaSource G) x) =
      intervalMappingUncurry (𝟙 (intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y))) := by
  change unitCommaUncurry (unitCommaFiberCurry G x (SSet.const y)
    (kanIntervalToUnitCommaHomotopy G x y) ≫ vertexFiberι (unitCommaSource G) x) = _
  rw [unitCommaFiberCurry_uncurry]
  change (β_ (Δ[1] : SSet.{u}) _).hom ≫ (β_ _ (Δ[1] : SSet.{u})).hom ≫ _ = _
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 概要：固定始域の comma の標的 fiber は両端固定の区間写像空間と厳密に同型。
方針：両方向の展開の計算を使い、comma 側は標的と矢印で、区間側は uncurry で両逆を確認する。
規約：充填性に依存しない単体集合の同型。
使われ方：局所 Kan 添字の比較の fiber を既存の区間比較に同定する。 -/
def kanUnitCommaFiberIntervalIso {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    vertexFiber (kanUnitCommaFiberProjection G x) y ≅
      intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) where
  hom := kanUnitCommaFiberToInterval G x y
  inv := kanIntervalToUnitCommaFiber G x y
  hom_inv_id := by
    apply vertexFiber_hom_ext (kanUnitCommaFiberProjection G x) y
    apply unitCommaFiber_hom_ext
    · change ((kanUnitCommaFiberToInterval G x y ≫ kanIntervalToUnitCommaFiber G x y) ≫
        vertexFiberι (kanUnitCommaFiberProjection G x) y) ≫ kanUnitCommaFiberProjection G x =
          (𝟙 _ ≫ vertexFiberι (kanUnitCommaFiberProjection G x) y) ≫
            kanUnitCommaFiberProjection G x
      simp only [Category.assoc, vertexFiberι_comp, SSet.comp_const]
    · change (β_ _ (Δ[1] : SSet.{u})).hom ≫ unitCommaUncurry
        (kanUnitCommaFiberToInterval G x y ≫ (kanIntervalToUnitCommaFiber G x y ≫
          vertexFiberι (kanUnitCommaFiberProjection G x) y ≫
            vertexFiberι (unitCommaSource G) x)) =
        (β_ _ (Δ[1] : SSet.{u})).hom ≫ unitCommaUncurry
          (vertexFiberι (kanUnitCommaFiberProjection G x) y ≫
            vertexFiberι (unitCommaSource G) x)
      rw [unitCommaUncurry_precomp, kanIntervalToUnitCommaFiber_uncurry,
        ← intervalMappingUncurry_precomp, Category.comp_id, kanUnitCommaFiberToInterval_uncurry]
  inv_hom_id := by
    apply intervalMappingUncurry_injective
    rw [intervalMappingUncurry_precomp, kanUnitCommaFiberToInterval_uncurry,
      ← unitCommaUncurry_precomp, kanIntervalToUnitCommaFiber_uncurry]

end SerrePositivity.InfinityCategories.F1B
