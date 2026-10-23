module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CylinderFixedEndpointSquares

/-!
概要：両端固定の四角形の端点を普遍 pointed-space fiber 値の写像として回収する。
方針：全空間の族を円柱の両端で制限し、固定された底の fiber へ持ち上げる。
規約：同値条件を課す前の全ての四角形を扱う。
使われ方：両端同値の部分空間の定義と逆比較の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：円柱の始点の包含。
方針：prism の時刻零を pushout の第一部分へ含める。
規約：始点の係数は K。
使われ方：始点の fiber 値の写像の回収。 -/
def cylinderSquareSourceInclusion {K J : SSet.{u}} (f : K ⟶ J) :
    K ⟶ pushout (prismEndpoint 1 K) f := prismEndpoint 0 K ≫ pushout.inl _ _

/-- 概要：円柱の始点の底は時刻零に定値。
方針：prism 部分の射影の公式を使う。
規約：射の厳密な等式。
使われ方：始点を s 上の fiber に持ち上げる。 -/
lemma cylinderSquareSourceInclusion_projection {K J : SSet.{u}} (f : K ⟶ J) :
    cylinderSquareSourceInclusion f ≫ mappingCylinderIntervalProjection f =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [cylinderSquareSourceInclusion, Category.assoc, mappingCylinderIntervalProjection_inl]
  rfl

/-- 概要：底の端点を指定した部分の評価は対応する普遍 fiber に入る。
方針：四角形の底の式を部分の射で引き戻し、端点公式を使う。
規約：i は零または一の任意の端点。
使われ方：二つの端点写像の共通の fiber 条件。 -/
lemma cylinderFixedEndpointSquare_restriction_base {K J A : SSet.{u + 1}} (f : K ⟶ J)
    (s t b : SpaceInfinity.{u} _⦋0⦌) (i : Fin 2)
    (j : A ⟶ pushout (prismEndpoint 1 K) f)
    (hj : j ≫ mappingCylinderIntervalProjection f = SSet.const (stdSimplex.obj₀Equiv.symm i))
    (hb : prismEndpoint i _ ≫ intervalMappingUncurry
      (cylinderFixedEndpointSquareInterval f s t) = SSet.const b) :
    ((j ▷ cylinderFixedEndpointSquareSpace f s t) ≫
        uncurry (cylinderFixedEndpointSquarePointed f s t)) ≫ pointedSpaceProjection =
      SSet.const b := by
  rw [Category.assoc, cylinderFixedEndpointSquare_base, ← Category.assoc,
    ← comp_whiskerRight, hj]
  change (snd A _ ≫ prismEndpoint i _) ≫
    intervalMappingUncurry (cylinderFixedEndpointSquareInterval f s t) = _
  rw [Category.assoc, hb, SSet.comp_const]

/-- 概要：両端固定四角形の始点を s 上の普遍 fiber への関手として回収する。
方針：始点の包含への制限を fiber に持ち上げて curry する。
規約：全高次パラメーターの族。
使われ方：始点同値の部分空間を指定する射。 -/
def cylinderFixedEndpointSquareSource {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareSpace f s t ⟶ (ihom K).obj (vertexFiber pointedSpaceProjection s) :=
  curry (vertexFiberLift pointedSpaceProjection s
    ((cylinderSquareSourceInclusion f ▷ _) ≫ uncurry (cylinderFixedEndpointSquarePointed f s t))
    (cylinderFixedEndpointSquare_restriction_base f s t s 0 _
      (cylinderSquareSourceInclusion_projection f) (intervalMappingUncurry_zero _)))

/-- 概要：両端固定四角形の終点を t 上の普遍 fiber への関手として回収する。
方針：pushout の終点部分への制限を fiber に持ち上げて curry する。
規約：全高次パラメーターの族。
使われ方：終点同値の部分空間を指定する射。 -/
def cylinderFixedEndpointSquareTarget {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareSpace f s t ⟶ (ihom J).obj (vertexFiber pointedSpaceProjection t) :=
  curry (vertexFiberLift pointedSpaceProjection t
    ((pushout.inr (prismEndpoint 1 K) f ▷ _) ≫ uncurry (cylinderFixedEndpointSquarePointed f s t))
    (cylinderFixedEndpointSquare_restriction_base f s t t 1 _
      (mappingCylinderIntervalProjection_inr f) (intervalMappingUncurry_one _)))

/-- 概要：始点の fiber 値の族を包含すると元の円柱の始点の制限。
方針：uncurry して fiber の持ち上げの包含公式を使う。
規約：射そのものの等式。
使われ方：逆比較の始点条件と順比較の端点の回収。 -/
lemma cylinderFixedEndpointSquareSource_ι {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareSource f s t ≫ (ihom K).map (vertexFiberι pointedSpaceProjection s) =
      cylinderFixedEndpointSquarePointed f s t ≫ (pre (cylinderSquareSourceInclusion f)).app _ := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app]
  change uncurry (curry _) ≫ _ = _
  rw [uncurry_curry, vertexFiberLift_ι]

/-- 概要：終点の fiber 値の族を包含すると元の円柱の終点の制限。
方針：uncurry して fiber の持ち上げの包含公式を使う。
規約：射そのものの等式。
使われ方：逆比較の終点条件と順比較の端点の回収。 -/
lemma cylinderFixedEndpointSquareTarget_ι {K J : SSet.{u + 1}} (f : K ⟶ J)
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    cylinderFixedEndpointSquareTarget f s t ≫ (ihom J).map (vertexFiberι pointedSpaceProjection t) =
      cylinderFixedEndpointSquarePointed f s t ≫
        (pre (pushout.inr (prismEndpoint 1 K) f)).app _ := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app]
  change uncurry (curry _) ≫ _ = _
  rw [uncurry_curry, vertexFiberLift_ι]

end SerrePositivity.InfinityCategories
