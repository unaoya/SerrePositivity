module
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetAt
public import SerrePositivity.KST.SConstruction.SimplexSubsetCubicalCell

/-! # 元の部分集合包含と次元を揃えた cubical 生成射
概要：元の同端点の包含を濃度−2 次元の実 cube 射にし、元の全生成射の可換性を得る。
方針：元の次元同型だけで共役し、元の余極限の表示関係を使う。
規約：元の実 cube 射と生成射を保持。使われ方：HA 削除面の Serre 鎖への移送。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の次元同型で cube 射を共役しても、元の同じ cell の可換三角形を保つ。 -/
lemma cubicalYoneda_conjugate_cell {P Q R S : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} {M : CubicalSet.{u}}
    (e : P ≅ Q) (e' : R ≅ S) (f : Q ⟶ S)
    (c : cubicalYoneda.obj Q ⟶ M) (d : cubicalYoneda.obj S ⟶ M)
    (h : cubicalYoneda.map f ≫ d = c) :
    cubicalYoneda.map (e.hom ≫ f ≫ e'.inv) ≫ (cubicalYoneda.map e'.hom ≫ d) =
      cubicalYoneda.map e.hom ≫ c := by
  simp only [Functor.map_comp, Category.assoc]
  change cubicalYoneda.map e.hom ≫ cubicalYoneda.map f ≫
    (cubicalYoneda.mapIso e').inv ≫ (cubicalYoneda.mapIso e').hom ≫ d = _
  rw [(cubicalYoneda.mapIso e').inv_hom_id_assoc, h]

/-- 元の指定した両端の Hom に値を持つ、同じ元の部分集合 cubical 生成射。 -/
def simplexSubsetCubicalCellAt {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    cubicalYoneda.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2)) ⟶
      necklaceCubicalMapping (Δ[n] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) :=
  cubicalYoneda.map (simplexSubsetCubeDimensionIso.{u} I hI).hom ≫
    necklaceCubicalCell (necklaceInSimplexSubsetAt I a b hI ha hb)

/-- 元の最小・最大端点に戻すと、元の同じ部分集合の生成射そのもの。 -/
lemma simplexSubsetCubicalCellAt_canonical {n : ℕ} (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) :
    simplexSubsetCubicalCellAt.{u} I (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
      (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) hI rfl rfl = simplexSubsetCubicalCell I hI := rfl

/-- 元の同端点の部分集合包含を、元の濃度−2 次元を持つ実 cube 射で読む。 -/
def simplexSubsetCubeInclusion {n : ℕ} (I J : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
    (haI : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hbI : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (haJ : a = J.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))
    (hbJ : b = J.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (I.card - 2) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (J.card - 2) :=
  (simplexSubsetCubeDimensionIso.{u} I hI).hom ≫
    necklaceConcreteCube.map
      (necklaceInSimplexSubsetAtInclusion.{u} I J a b hI hJ hIJ haI hbI haJ hbJ).necklaceHom ≫
        (simplexSubsetCubeDimensionIso.{u} J hJ).inv

/-- 元の次元を揃えた部分集合包含は、元の同じ HA 用 cubical 生成射と厳密に可換。 -/
lemma simplexSubsetCubeInclusion_cell {n : ℕ} (I J : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
    (haI : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hbI : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (haJ : a = J.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ))
    (hbJ : b = J.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty J hJ)) :
    cubicalYoneda.map (simplexSubsetCubeInclusion.{u} I J a b hI hJ hIJ haI hbI haJ hbJ) ≫
        simplexSubsetCubicalCellAt J a b hJ haJ hbJ =
      simplexSubsetCubicalCellAt I a b hI haI hbI :=
  cubicalYoneda_conjugate_cell (simplexSubsetCubeDimensionIso.{u} I hI)
    (simplexSubsetCubeDimensionIso.{u} J hJ)
    (necklaceConcreteCube.map
      (necklaceInSimplexSubsetAtInclusion.{u} I J a b hI hJ hIJ haI hbI haJ hbJ).necklaceHom)
    _ _ (necklaceInSimplexSubsetAtInclusion_cell I J a b hI hJ hIJ haI hbI haJ hbJ)

end SerrePositivity.KST.SConstruction
