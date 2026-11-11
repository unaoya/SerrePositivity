module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.DistinguishedRotation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.DistinguishedCoconeTriangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IdentityCofiber
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangleMorphismExtension
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # 安定 ∞ 圏のホモトピー圏の前三角構造

概要：安定 quasicategory のホモトピー圏に Mathlib の Pretriangulated instance を与える。
方針：cofiber 三角形の同型閉包について証明した TR1・TR2・TR3 を束ねる。
規約：前加法構造・整数シフトは既存のもの。八面体公理 TR4 は別途必要。
使われ方：長完全列と三角関手、および三角圏構造の八面体公理。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Pretriangulated SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：安定 quasicategory のホモトピー圏は cofiber 列の像による前三角構造を持つ。
方針：同型閉性、可縮三角形、任意の射の三角形、回転の同値、射の延長を各証明から取る。
規約：TR4 はこの instance の主張に含まれない。使われ方：Mathlib の前三角圏の一般論。 -/
instance pretriangulated_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    Pretriangulated (hoFunctor.obj X) where
  distinguishedTriangles := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X
  isomorphic_distinguished _ h _ e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.mem_cofiberDistinguishedTriangles_of_iso e.symm h
  contractible_distinguished := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.contractibleTriangle_mem_cofiberDistinguishedTriangles
  distinguished_cocone_triangle := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_cofiberDistinguishedTriangle
  rotate_distinguished_triangle := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles_rotate_iff
  complete_distinguished_triangle_morphism _ _ hT hU a b h :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.complete_cofiberDistinguishedTriangle_morphism hT hU a b h

/-- 概要：公開した前三角構造の distinguished triangles は cofiber 列の像の集合そのもの。
方針：instance の定義を展開する。
規約：対象・シフト・三射を変えない。使われ方：幾何学的な所属と Mathlib の所属の往復。 -/
lemma distinguishedTriangles_ho_eq {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    (distinguishedTriangles : Set (Triangle (hoFunctor.obj X))) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X := rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
