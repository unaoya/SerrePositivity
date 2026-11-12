module
public import SerrePositivity.KST.SConstruction.SimplexIntervalComposeOneFace
public import SerrePositivity.KST.SConstruction.SimplexHAStrictIntervalSplit

/-! # 元の二区間合成 cube の標準区間次元表示
概要：元の necklace 合成 cube の始域と終域を、同じ元の区間内部次元へ移す。
方針：元の共有頂点一面の式に、同じ両次元の等号移送を適用する。
規約：元の右端座標と全射を保持。使われ方：Λ 合成と HA 内部一面の実鎖射比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
universe u

/-- 元の二区間内部次元の和は、同じ連結 necklace の元の次元。 -/
lemma simplexIntervalCompose_source_dimension {N : ℕ} (a b c : Fin (N + 1)) :
    (b.val - a.val - 1) + (c.val - b.val - 1) =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
        (necklaceBead (c.val - b.val))).down.dimension := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (b.val - a.val)).wedge_dimension
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single (c.val - b.val))
  have hp := necklaceBead_dimension.{u} (b.val - a.val)
  have hq := necklaceBead_dimension.{u} (c.val - b.val)
  exact ((congrArg₂ Nat.add hp hq).symm.trans h.symm)

/-- 元の実二区間合成 cube を、同じ左右・全区間の内部次元で読む。 -/
def simplexIntervalComposeStandardCube {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((b.val - a.val - 1) + (c.val - b.val - 1)) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (c.val - a.val - 1) :=
  (concreteCubeDimensionIso
    (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((b.val - a.val - 1) + (c.val - b.val - 1)))
    (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
      (necklaceBead (c.val - b.val))).down.dimension)
    (simplexIntervalCompose_source_dimension.{u} a b c)).hom ≫
      necklaceConcreteCubeMap (simplexIntervalComposeBeadHom.{u} a b c hab.le hbc.le) ≫
        (concreteCubeDimensionIso
          (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (c.val - a.val - 1))
          (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} (c.val - a.val)).down.dimension)
          (necklaceBead_dimension.{u} (c.val - a.val)).symm).inv

/-- 元の標準区間次元の実合成は、同じ共有頂点の右端座標の標準一面を回収。 -/
lemma simplexIntervalComposeStandardCube_one_face {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    simplexIntervalComposeStandardCube.{u} a b c hab hbc ≫
      (concreteCubeDimensionIso
        (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (c.val - a.val - 1))
        (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (((b.val - a.val - 1) + (c.val - b.val - 1)) + 1))
        (by
          change c.val - a.val - 1 = ((b.val - a.val - 1) + (c.val - b.val - 1)) + 1
          have h := simplexHAStrictInterval_split_dimension a b c hab hbc
          omega)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true ((b.val - a.val - 1) + (c.val - b.val - 1))
        ⟨c.val - b.val - 1, by omega⟩ := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
    (necklaceBead (c.val - b.val))
  have hm := simplexIntervalCompose_source_dimension.{u} a b c
  have hn := (necklaceBead_dimension.{u} (c.val - a.val)).symm
  have hc := simplexIntervalCompose_codimension.{u} a b c hab hbc
  have hc' : c.val - a.val - 1 =
      ((b.val - a.val - 1) + (c.val - b.val - 1)) + 1 := by
    have h := simplexHAStrictInterval_split_dimension a b c hab hbc
    omega
  let i := Fin.cast hc.symm (simplexIntervalComposeCoordinate.{u} a b c hab hbc)
  have hf : necklaceConcreteCubeMap
      (simplexIntervalComposeBeadHom.{u} a b c hab.le hbc.le) ≫
      (concreteCubeDimensionIso
        (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} (c.val - a.val)).down.dimension)
        (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + 1)) hc).hom =
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true T.down.dimension (Fin.cast hc i) := by
    have hi : Fin.cast hc i = simplexIntervalComposeCoordinate.{u} a b c hab hbc :=
      Fin.ext rfl
    exact (simplexIntervalCompose_cube_one_face.{u, u} a b c hab hbc).trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true T.down.dimension) hi.symm)
  have h := concreteCube_face_conjugate true hm hn hc hc'
    (necklaceConcreteCubeMap (simplexIntervalComposeBeadHom.{u} a b c hab.le hbc.le)) i hf
  have hi : Fin.cast hc' (Fin.cast hn.symm i) =
      (⟨c.val - b.val - 1, by omega⟩ :
        Fin (((b.val - a.val - 1) + (c.val - b.val - 1)) + 1)) := Fin.ext rfl
  exact h.trans (congrArg (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true
    ((b.val - a.val - 1) + (c.val - b.val - 1))) hi)

end SerrePositivity.KST.SConstruction
