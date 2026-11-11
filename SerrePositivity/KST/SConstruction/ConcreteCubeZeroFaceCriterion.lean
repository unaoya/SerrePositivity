module
public import SerrePositivity.KST.SConstruction.ConcreteCubeDimensionIso
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Fin.Basic

/-! # 元の単調座標埋め込みによる零面の判定
概要：元の cube 射が一つの欠落座標に零を入れ、全残存座標を保つなら元の標準零面。
方針：元の座標順と像から succAbove を一意に決め、元の全頂点関数で射を判定する。
規約：次元の等号は元の構造同型だけで移す。使われ方：内部点削除の数値零面。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の一座標だけを欠く順序埋め込みは、同じ元の succAbove そのもの。 -/
lemma cubeCoordinateEmbedding_eq_succAbove {m : ℕ} (e : Fin m ↪o Fin (m + 1))
    (i : Fin (m + 1)) (hr : Set.range e = {i}ᶜ) : e = Fin.succAboveOrderEmb i :=
  OrderEmbedding.eq_of_range_eq (hr.trans (Fin.range_succAboveOrderEmb i).symm)

/-- 元の一座標に零を入れ、順序を保つ全残存座標を保持する実 cube 射は元の標準零面。 -/
lemma concreteCube_zero_face_of_coordinate_embedding {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n) (e : Fin m ↪o Fin n) (i : Fin n)
    (hn : n = m + 1) (hr : Set.range e = {i}ᶜ)
    (hz : ∀ x, f.val x i = false) (he : ∀ x j, f.val x (e j) = x j) :
    f ≫ (concreteCubeDimensionIso
      (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n) (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (m + 1)) hn).hom =
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace false m (Fin.cast hn i) := by
  subst n
  have h := cubeCoordinateEmbedding_eq_succAbove e i hr
  subst e
  apply Subtype.ext
  funext x j
  change f.val x j = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace false m i x j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_apply_same] using hz x
  · simpa only [Fin.coe_succAboveOrderEmb, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_apply_succAbove]
      using he x k

/-- 元の零面の同定は、始域・終域の元の次元同型による共役でも保たれる。 -/
lemma concreteCube_zero_face_conjugate {m n m' n' : ℕ} (hm : m' = m) (hn : n' = n)
    (hc : n = m + 1) (hc' : n' = m' + 1)
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n) (i : Fin n)
    (hf : f ≫ (concreteCubeDimensionIso
      (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n) (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (m + 1)) hc).hom =
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace false m (Fin.cast hc i)) :
    ((concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m') (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m) hm).hom ≫
        f ≫ (concreteCubeDimensionIso
          (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n') (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n) hn).inv) ≫
      (concreteCubeDimensionIso
        (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n') (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (m' + 1)) hc').hom =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace false m' (Fin.cast hc' (Fin.cast hn.symm i)) := by
  subst m'
  subst n'
  simpa only [concreteCubeDimensionIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id, Fin.cast_refl, id_eq] using hf

end SerrePositivity.KST.SConstruction
