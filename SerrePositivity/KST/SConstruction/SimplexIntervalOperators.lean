module
public import SerrePositivity.KST.SConstruction.NecklaceSimplexIntervalTerminal
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklacePostcomposition

/-! # 元の全単体作用素が区間 bead に誘導する射
概要：面・退化を含む元の単体圏の全射を、同じ像区間の実 necklace 射へ送る。
方針：元の後合成と区間 bead の終対象性を使い、元の可換三角形を保つ。
規約：頂点が潰れる場合も含む。使われ方：全区間 Hom 比較の単体的自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の全単体作用素は、番号で指定した元の零単体を同じ像の零単体へ送る。 -/
lemma standardSimplexVertex_map {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (a : Fin (m + 1)) :
    (stdSimplex.{u}.map θ).app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (θ.toOrderHom a) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext rfl

/-- 元の区間 bead の augmentation を全単体作用素で後合成した、像端点間の necklace。 -/
def simplexIntervalImageNecklace {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) (hab : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u})
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (θ.toOrderHom a)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (θ.toOrderHom b)) where
  necklace := necklaceBead.{u} (b.val - a.val)
  map := (necklaceInSimplexInterval a b hab).map ≫ stdSimplex.map θ
  map_first := (congrArg ((stdSimplex.{u}.map θ).app _)
    (necklaceInSimplexInterval.{u} a b hab).map_first).trans
      (standardSimplexVertex_map θ a)
  map_last := (congrArg ((stdSimplex.{u}.map θ).app _)
    (necklaceInSimplexInterval.{u} a b hab).map_last).trans
      (standardSimplexVertex_map θ b)

/-- 元の全単体作用素の区間 bead 間の作用は、元の像区間への実可換三角形の射。 -/
def simplexIntervalBeadMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) (hab : a ≤ b) :
    necklaceBead.{u} (b.val - a.val) ⟶
      necklaceBead ((θ.toOrderHom b).val - (θ.toOrderHom a).val) :=
  (necklaceInToSimplexInterval (θ.toOrderHom a) (θ.toOrderHom b)
    (θ.toOrderHom.monotone hab) (simplexIntervalImageNecklace θ a b hab)).necklaceHom

/-- 元の区間の全高次単体の作用を、元の標準単体の射との可換三角形で回収する。 -/
lemma simplexIntervalBeadMap_triangle {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) (hab : a ≤ b) :
    (simplexIntervalBeadMap.{u} θ a b hab).map ≫
        (necklaceInSimplexInterval (θ.toOrderHom a) (θ.toOrderHom b)
          (θ.toOrderHom.monotone hab)).map =
      (necklaceInSimplexInterval a b hab).map ≫ stdSimplex.map θ :=
  (necklaceInToSimplexInterval (θ.toOrderHom a) (θ.toOrderHom b)
    (θ.toOrderHom.monotone hab) (simplexIntervalImageNecklace θ a b hab)).w

/-- 元の全単体作用素が誘導する区間射の頂点番号は、元の像の始端を引いた番号。 -/
lemma simplexIntervalBeadMap_vertex {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (m + 1)) (hab : a ≤ b)
    (v : (necklaceBead.{u} (b.val - a.val)).down.Vertex) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (simplexIntervalBeadMap.{u} θ a b hab) v).val =
      (θ.toOrderHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder a b hab v)).val - (θ.toOrderHom a).val := rfl

/-- 元の恒等単体作用素は、元の区間 bead の恒等射を誘導する。 -/
lemma simplexIntervalBeadMap_id {m : ℕ} (a b : Fin (m + 1)) (hab : a ≤ b) :
    simplexIntervalBeadMap.{u} (𝟙 ⦋m⦌) a b hab = 𝟙 (necklaceBead (b.val - a.val)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext
  apply (cancel_mono (necklaceInSimplexInterval a b hab).map).1
  exact (simplexIntervalBeadMap_triangle (𝟙 ⦋m⦌) a b hab).trans
    ((congrArg (fun f => (necklaceInSimplexInterval a b hab).map ≫ f)
      (stdSimplex.{u}.map_id ⦋m⦌)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- 元の単体作用素の合成は、元の区間 bead の実射の合成を厳密に保つ。 -/
lemma simplexIntervalBeadMap_comp {l m n : ℕ} (θ : ⦋l⦌ ⟶ ⦋m⦌) (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (a b : Fin (l + 1)) (hab : a ≤ b) :
    simplexIntervalBeadMap.{u} (θ ≫ φ) a b hab =
      simplexIntervalBeadMap.{u} θ a b hab ≫
        simplexIntervalBeadMap.{u} φ (θ.toOrderHom a) (θ.toOrderHom b)
          (θ.toOrderHom.monotone hab) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext
  apply (cancel_mono (necklaceInSimplexInterval ((θ ≫ φ).toOrderHom a)
    ((θ ≫ φ).toOrderHom b) ((θ ≫ φ).toOrderHom.monotone hab)).map).1
  change (simplexIntervalBeadMap.{u} (θ ≫ φ) a b hab).map ≫ _ =
    ((simplexIntervalBeadMap.{u} θ a b hab).map ≫
      (simplexIntervalBeadMap.{u} φ (θ.toOrderHom a) (θ.toOrderHom b)
        (θ.toOrderHom.monotone hab)).map) ≫ _
  exact (simplexIntervalBeadMap_triangle (θ ≫ φ) a b hab).trans
    ((congrArg (fun f => (necklaceInSimplexInterval a b hab).map ≫ f)
      (stdSimplex.{u}.map_comp θ φ)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ stdSimplex.map φ)
            (simplexIntervalBeadMap_triangle θ a b hab).symm).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (fun f => (simplexIntervalBeadMap.{u} θ a b hab).map ≫ f)
                  (simplexIntervalBeadMap_triangle φ (θ.toOrderHom a) (θ.toOrderHom b)
                    (θ.toOrderHom.monotone hab)).symm).trans
                      (Category.assoc _ _ _).symm)))))

end SerrePositivity.KST.SConstruction
