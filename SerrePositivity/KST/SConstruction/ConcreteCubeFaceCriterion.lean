module
public import SerrePositivity.KST.SConstruction.ConcreteCubeZeroFaceCriterion

/-! # 元の全端点面の数値座標による判定
概要：元の一座標に指定端点を入れ、順序を保つ全残存座標を保持する射は標準の同じ面。
方針：元の座標順と像による succAbove の一意性を、元の全頂点上で使う。
規約：零面・一面に同じ座標向きを用いる。使われ方：分割合成の標準一面。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の一座標に指定端点を入れ、元の全残存座標を保持する実 cube 射は標準の同じ面。 -/
lemma concreteCube_face_of_coordinate_embedding {m n : ℕ} (b : Bool)
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n) (e : Fin m ↪o Fin n) (i : Fin n)
    (hn : n = m + 1) (hr : Set.range e = {i}ᶜ)
    (hz : ∀ x, f.val x i = b) (he : ∀ x j, f.val x (e j) = x j) :
    f ≫ (concreteCubeDimensionIso
      (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n) (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (m + 1)) hn).hom =
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b m (Fin.cast hn i) := by
  subst n
  have h := cubeCoordinateEmbedding_eq_succAbove e i hr
  subst e
  apply Subtype.ext
  funext x j
  change f.val x j = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b m i x j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_apply_same] using hz x
  · simpa only [Fin.coe_succAboveOrderEmb, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_apply_succAbove]
      using he x k

end SerrePositivity.KST.SConstruction
