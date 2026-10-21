module
public import SerrePositivity.KST.SConstruction.NecklaceWedgeBooleanJoin
public import SerrePositivity.KST.SConstruction.NecklaceWedgeVertices
public import SerrePositivity.KST.SConstruction.NecklaceBooleanMap

/-! # 元の全 necklace 射の連結と Bool 座標作用
概要：元の wedge 射の Bool 作用が、左右の元の作用の連結と一致すると示す。
方針：全頂点のファイバー表示を使い、反対側の像を共有点での順序分離で除く。
規約：joint 像の定数一も保持。使われ方：全具体的 cube 射の tensor 自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の全連結射の左出力は、元の左射の Bool 座標作用そのもの。 -/
lemma necklaceBooleanMap_wedge_left {T T' U U' : Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U')
    (b : T.down.NonjointVertex → Bool) (c : U.down.NonjointVertex → Bool)
    (v : T'.down.NonjointVertex) :
    necklaceBooleanMap (necklaceWedgeMap f g) (T.down.wedgeBooleanJoin U.down b c)
      (T'.down.wedgeNonjointLeft U'.down v) = necklaceBooleanMap f b v := by
  apply Bool.eq_iff_iff.mpr
  rw [necklaceBooleanMap_true_iff, necklaceBooleanMap_true_iff]
  constructor
  · rintro ⟨j, hj, he⟩
    rcases T.down.wedgeVertex_cases U.down j with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [NecklaceShape.cubeFullBits_wedge_left] at hj
      rw [necklaceVertexMap_wedge_left] at he
      have he' := congrArg Fin.val he
      exact ⟨a, hj, Fin.ext he'⟩
    · rw [necklaceVertexMap_wedge_right] at he
      have hv := T'.down.wedgeNonjointLeft_lt_seam U'.down v
      have hv' := congrArg Fin.val he
      change T'.down.vertexMax + (necklaceVertexMap g a).val = v.val.val at hv'
      change v.val.val < T'.down.vertexMax at hv
      omega
  · rintro ⟨a, ha, he⟩
    refine ⟨T.down.wedgeLeftVertex U.down a, ?_, ?_⟩
    · simpa only [NecklaceShape.cubeFullBits_wedge_left] using ha
    · rw [necklaceVertexMap_wedge_left, he]
      rfl

/-- 元の全連結射の右出力は、元の右射の Bool 座標作用そのもの。 -/
lemma necklaceBooleanMap_wedge_right {T T' U U' : Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U')
    (b : T.down.NonjointVertex → Bool) (c : U.down.NonjointVertex → Bool)
    (v : U'.down.NonjointVertex) :
    necklaceBooleanMap (necklaceWedgeMap f g) (T.down.wedgeBooleanJoin U.down b c)
      (T'.down.wedgeNonjointRight U'.down v) = necklaceBooleanMap g c v := by
  apply Bool.eq_iff_iff.mpr
  rw [necklaceBooleanMap_true_iff, necklaceBooleanMap_true_iff]
  constructor
  · rintro ⟨j, hj, he⟩
    rcases T.down.wedgeVertex_cases U.down j with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [necklaceVertexMap_wedge_left] at he
      have hv := T'.down.seam_lt_wedgeNonjointRight U'.down v
      have hv' := congrArg Fin.val he
      have hb := (necklaceVertexMap f a).isLt
      change (necklaceVertexMap f a).val = T'.down.vertexMax + v.val.val at hv'
      change T'.down.vertexMax < T'.down.vertexMax + v.val.val at hv
      omega
    · rw [NecklaceShape.cubeFullBits_wedge_right] at hj
      rw [necklaceVertexMap_wedge_right] at he
      have he' := congrArg Fin.val he
      change T'.down.vertexMax + (necklaceVertexMap g a).val =
        T'.down.vertexMax + v.val.val at he'
      exact ⟨a, hj, Fin.ext (by omega)⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨T.down.wedgeRightVertex U.down a, ?_, ?_⟩
    · simpa only [NecklaceShape.cubeFullBits_wedge_right] using ha
    · rw [necklaceVertexMap_wedge_right, he]
      rfl

/-- 全元の非 joint 座標で、連結射の Bool 作用は左右の元の作用の連結に一致する。 -/
lemma necklaceBooleanMap_wedge_join {T T' U U' : Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U')
    (b : T.down.NonjointVertex → Bool) (c : U.down.NonjointVertex → Bool) :
    necklaceBooleanMap (necklaceWedgeMap f g) (T.down.wedgeBooleanJoin U.down b c) =
      T'.down.wedgeBooleanJoin U'.down (necklaceBooleanMap f b) (necklaceBooleanMap g c) := by
  funext v
  obtain ⟨a, rfl⟩ := (T'.down.wedgeNonjointEquiv U'.down).surjective v
  rcases a with a | a
  · exact (necklaceBooleanMap_wedge_left f g b c a).trans
      (T'.down.wedgeBooleanJoin_left U'.down _ _ a).symm
  · exact (necklaceBooleanMap_wedge_right f g b c a).trans
      (T'.down.wedgeBooleanJoin_right U'.down _ _ a).symm

end SerrePositivity.KST.SConstruction
