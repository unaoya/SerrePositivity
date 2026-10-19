module
public import SerrePositivity.KST.SConstruction.EdgeSegalEquivalence
public import SerrePositivity.KST.SConstruction.IteratedPathBoundary

/-! # 先頭を保つ経路作用素の Segal 積座標
概要：経路の各行を境界の行と最初の辺の積に比較し、先頭を保つ作用素で厳密に可換にする。
方針：一番目での切断の二評価を入れ替え、先頭追加写像の二頂点での値を照合する。
規約：先頭を送る条件を明示し、一般の面条件の完成とは区別する。
使われ方：先頭を保つ経路面のホモトピー引き戻し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 先頭を保つ単体作用素の経路への作用は最初の辺への制限と厳密に可換。 -/
lemma pathFirstEdge_naturality {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (hθ : θ.toOrderHom 0 = 0) (X : StableModel.{u}) :
    (sEndofunctorMap (SimplexPrefix.functor.map θ).toOrderHom).app X ≫
      cutLeftSegalEvaluation (m + 1) ⟨1, by omega⟩ X =
    cutLeftSegalEvaluation (n + 1) ⟨1, by omega⟩ X := by
  have hi : (SimplexPrefix.functor.map θ).toOrderHom.comp
      (cutLeftIntervalInclusion (m + 1) ⟨1, by omega⟩) =
    cutLeftIntervalInclusion (n + 1) ⟨1, by omega⟩ := by
    apply DFunLike.ext
    intro j
    fin_cases j
    · rfl
    · change (θ.toOrderHom 0).succ = (0 : Fin (n + 1)).succ
      rw [hθ]
  apply Subtype.ext
  change sMap X.carrier (SimplexPrefix.functor.map θ).toOrderHom ≫
    sMap X.carrier (cutLeftIntervalInclusion (m + 1) ⟨1, by omega⟩) = _
  rw [← sMap_comp, hi]
  rfl

/-- 経路の各行を元の境界行と最初の辺の積へ比較する元の二区間評価。 -/
def pathHeadSegalMap (r n : ℕ) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram (r + 1) X).obj (Opposite.op ⦋n⦌) ⟶
      (iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋n⦌) ⊗
        (multiRealizationFunctor (r + 1)).obj (sStableModel 1 X) :=
  CartesianMonoidalCategory.lift ((iteratedPathBoundary (r + 1) X).app (Opposite.op ⦋n⦌))
    ((multiRealizationFunctor (r + 1)).map
      (cutLeftSegalEvaluation (n + 1) ⟨1, by omega⟩ X))

/-- 積座標の第一射影は元の経路境界そのもの。 -/
lemma pathHeadSegalMap_fst (r n : ℕ) (X : StableModel.{u}) :
    pathHeadSegalMap r n X ≫ CartesianMonoidalCategory.fst _ _ =
      (iteratedPathBoundary (r + 1) X).app (Opposite.op ⦋n⦌) :=
  CartesianMonoidalCategory.lift_fst _ _

/-- 各行の経路の Segal 積座標への元の比較は局所化同型。 -/
lemma pathHeadSegalMap_localized_isIso (r n : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (pathHeadSegalMap r n X)) := by
  let F := multiRealizationFunctor (r + 1)
  have hC := cutSegalMap_localized_isIso r (n + 1) ⟨1, by omega⟩ X
  have he : pathHeadSegalMap r n X = cutSegalMap r (n + 1) ⟨1, by omega⟩ X ≫
      (β_ (F.obj (sStableModel 1 X)) (F.obj (sStableModel n X))).hom := by
    change CartesianMonoidalCategory.lift
      (F.map (cutRightSegalEvaluation (n + 1) ⟨1, by omega⟩ X))
      (F.map (cutLeftSegalEvaluation (n + 1) ⟨1, by omega⟩ X)) =
        CartesianMonoidalCategory.lift
          (F.map (cutLeftSegalEvaluation (n + 1) ⟨1, by omega⟩ X))
          (F.map (cutRightSegalEvaluation (n + 1) ⟨1, by omega⟩ X)) ≫ _
    exact (CartesianMonoidalCategory.lift_braiding_hom _ _).symm
  rw [he, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

/-- 先頭を保つ全単体作用素で経路の積座標は厳密に可換。 -/
lemma pathHeadSegalMap_naturality (r : ℕ) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (hθ : θ.toOrderHom 0 = 0) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram (r + 1) X).map θ.op ≫ pathHeadSegalMap r m X =
      pathHeadSegalMap r n X ≫
        ((iteratedSRealizationDiagram (r + 1) X).map θ.op ▷
          (multiRealizationFunctor (r + 1)).obj (sStableModel 1 X)) := by
  let F := multiRealizationFunctor (r + 1)
  change _ ≫ CartesianMonoidalCategory.lift _ _ = CartesianMonoidalCategory.lift _ _ ≫ _
  rw [CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.lift_whiskerRight]
  congr 1
  · exact (iteratedPathBoundary (r + 1) X).naturality θ.op
  · change F.map ((sEndofunctorMap (SimplexPrefix.functor.map θ).toOrderHom).app X) ≫
      F.map (cutLeftSegalEvaluation (m + 1) ⟨1, by omega⟩ X) = _
    rw [← F.map_comp, pathFirstEdge_naturality θ hθ]

end SerrePositivity.KST.SConstruction
