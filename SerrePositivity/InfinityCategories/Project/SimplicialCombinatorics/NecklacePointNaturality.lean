module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceWedgeMaps

/-! # 元の一点からの necklace 写像の自然性
概要：任意の単体的写像の定値単体上の作用を、元の零単体の像から回収する。
方針：各次数から一点への単体作用素との自然性を使う。
規約：順序写像由来の射に限定しない。使われ方：全 necklace 射の wedge。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

open CategoryTheory Opposite _root_.Simplicial SSet

/-- 全高次の定値単体への作用は、同じ零単体の像の退化である。 -/
lemma map_constantSimplex {T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape} {K : SSet.{u}}
    (f : T.carrier.{u} ⟶ K) (v : T.Vertex) (n : ℕ) :
    f.app _ (T.constantSimplex v n) =
      K.map (show ⦋n⦌ ⟶ ⦋0⦌ from
        SimplexCategory.Hom.mk (OrderHom.const (Fin (n + 1)) (0 : Fin 1))).op
        (f.app _ (T.constantSimplex v 0)) := by
  exact ConcreteCategory.congr_hom (f.naturality
    (show ⦋n⦌ ⟶ ⦋0⦌ from
      SimplexCategory.Hom.mk (OrderHom.const (Fin (n + 1)) (0 : Fin 1))).op)
    (T.constantSimplex v 0)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (map_constantSimplex)


/-- 一点からの二つの後合成は、元の零単体の像が等しければ全単体で等しい。 -/
lemma pointMap_comp_eq {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape} {K : SSet.{u}}
    (v : T.Vertex) (w : U.Vertex) (f : T.carrier.{u} ⟶ K) (g : U.carrier.{u} ⟶ K)
    (h : f.app _ (T.constantSimplex v 0) = g.app _ (U.constantSimplex w 0)) :
    T.pointMap v ≫ f = U.pointMap w ≫ g := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  change f.app _ ((T.pointMap v).app _ s) = g.app _ ((U.pointMap w).app _ s)
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap_app, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap_app, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.map_constantSimplex f v n, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.map_constantSimplex g w n, h]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (pointMap_comp_eq)


/-- 任意の元の necklace 写像に関する一点の像の自然性。 -/
lemma pointMap_naturality {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape} (f : T.carrier.{u} ⟶ U.carrier.{u})
    (v : T.Vertex) (w : U.Vertex)
    (h : f.app _ (T.constantSimplex v 0) = U.constantSimplex w 0) :
    T.pointMap v ≫ f = U.pointMap w := by
  simpa only [Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap_comp_eq v w f (𝟙 _) h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (pointMap_naturality)


/-- 左包含は元の連結の始頂点を回収する。 -/
lemma wedgeInl_first (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    (T.wedgeInl.{u} U).app _ T.firstVertex = (T.wedge U).firstVertex := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeInl_first)


/-- 右包含は元の連結の終頂点を回収する。 -/
lemma wedgeInr_last (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    (T.wedgeInr.{u} U).app _ U.lastVertex = (T.wedge U).lastVertex := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeInr_last)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.map_constantSimplex := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.map_constantSimplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.pointMap_comp_eq := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap_comp_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.pointMap_naturality := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap_naturality

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInl_first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInr_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_last
