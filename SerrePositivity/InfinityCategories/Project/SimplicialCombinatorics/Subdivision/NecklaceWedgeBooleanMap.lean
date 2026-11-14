module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeBooleanJoin
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeVertices
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceBooleanMap

/-! # 元の全 necklace 射の連結と Bool 座標作用
概要：元の wedge 射の Bool 作用が、左右の元の作用の連結と一致すると示す。
方針：全頂点のファイバー表示を使い、反対側の像を共有点での順序分離で除く。
規約：joint 像の定数一も保持。使われ方：全具体的 cube 射の tensor 自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の全連結射の左出力は、元の左射の Bool 座標作用そのもの。 -/
lemma necklaceBooleanMap_wedge_left {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U')
    (b : T.down.NonjointVertex → Bool) (c : U.down.NonjointVertex → Bool)
    (v : T'.down.NonjointVertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g) (T.down.wedgeBooleanJoin U.down b c)
      (T'.down.wedgeNonjointLeft U'.down v) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap f b v := by
  apply Bool.eq_iff_iff.mpr
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_true_iff, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_true_iff]
  constructor
  · rintro ⟨j, hj, he⟩
    rcases T.down.wedgeVertex_cases U.down j with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeFullBits_wedge_left] at hj
      rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_left] at he
      have he' := congrArg Fin.val he
      exact ⟨a, hj, Fin.ext he'⟩
    · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_right] at he
      have hv := T'.down.wedgeNonjointLeft_lt_seam U'.down v
      have hv' := congrArg Fin.val he
      change T'.down.vertexMax + (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap g a).val = v.val.val at hv'
      change v.val.val < T'.down.vertexMax at hv
      omega
  · rintro ⟨a, ha, he⟩
    refine ⟨T.down.wedgeLeftVertex U.down a, ?_, ?_⟩
    · simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeFullBits_wedge_left] using ha
    · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_left, he]
      rfl

/-- 元の全連結射の右出力は、元の右射の Bool 座標作用そのもの。 -/
lemma necklaceBooleanMap_wedge_right {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U')
    (b : T.down.NonjointVertex → Bool) (c : U.down.NonjointVertex → Bool)
    (v : U'.down.NonjointVertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g) (T.down.wedgeBooleanJoin U.down b c)
      (T'.down.wedgeNonjointRight U'.down v) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap g c v := by
  apply Bool.eq_iff_iff.mpr
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_true_iff, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_true_iff]
  constructor
  · rintro ⟨j, hj, he⟩
    rcases T.down.wedgeVertex_cases U.down j with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_left] at he
      have hv := T'.down.seam_lt_wedgeNonjointRight U'.down v
      have hv' := congrArg Fin.val he
      have hb := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f a).isLt
      change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f a).val = T'.down.vertexMax + v.val.val at hv'
      change T'.down.vertexMax < T'.down.vertexMax + v.val.val at hv
      omega
    · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeFullBits_wedge_right] at hj
      rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_right] at he
      have he' := congrArg Fin.val he
      change T'.down.vertexMax + (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap g a).val =
        T'.down.vertexMax + v.val.val at he'
      exact ⟨a, hj, Fin.ext (by omega)⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨T.down.wedgeRightVertex U.down a, ?_, ?_⟩
    · simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeFullBits_wedge_right] using ha
    · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_right, he]
      rfl

/-- 全元の非 joint 座標で、連結射の Bool 作用は左右の元の作用の連結に一致する。 -/
lemma necklaceBooleanMap_wedge_join {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U')
    (b : T.down.NonjointVertex → Bool) (c : U.down.NonjointVertex → Bool) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g) (T.down.wedgeBooleanJoin U.down b c) =
      T'.down.wedgeBooleanJoin U'.down (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap f b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap g c) := by
  funext v
  obtain ⟨a, rfl⟩ := (T'.down.wedgeNonjointEquiv U'.down).surjective v
  rcases a with a | a
  · exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_wedge_left f g b c a).trans
      (T'.down.wedgeBooleanJoin_left U'.down _ _ a).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_wedge_right f g b c a).trans
      (T'.down.wedgeBooleanJoin_right U'.down _ _ a).symm

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanMap_wedge_join := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_wedge_join

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanMap_wedge_left := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_wedge_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanMap_wedge_right := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_wedge_right
