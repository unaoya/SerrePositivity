module

public import SerrePositivity.KST.Spectra.MappingFiberPaths
public import SerrePositivity.KST.Spectra.FibrationAdjacentFiberEndpoint
public import SerrePositivity.KST.Spectra.PenultimateConnecting

/-!
概要：loop の連結射の持ち上げを path の比較ホーンの入力に移す。
方針：loop を path へ含め、Hom–fiber 同型と包含の自然性で境界代表を計算する。
規約：全て単体の厳密な等式。群の交換式を入力として仮定しない。
使われ方：Goerss–Jardine I §8。連結射の交換比較における非定数面の同定。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.LoopConnectingComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) {n : ℕ}
  {v : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right.PtSimplex (n + 1)
    ((PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right.app _
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint)}
  (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint v)

/-- loop の底の基点は path へ含めると射影された定数 path の基点となる。 -/
lemma sourcePoint :
    (PointedMapping.loopToPath B).right.app _
        ((PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right.app _
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint) =
      (basedPathMap p).right.app _ (basedPathSpace E).basepoint := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint,
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint]

/-- loop の底の単体を path の底の単体へ含める。 -/
def pathSimplex : (basedPathSpace B).right.PtSimplex (n + 1)
    ((basedPathMap p).right.app _ (basedPathSpace E).basepoint) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (PointedMapping.loopToPath B).right (sourcePoint p) v

/-- 概要：loop の相対ホーン充填を path の射影の相対ホーン充填へ移す。
方針：loop の path 表示の自然性と点つき基点保存を使う。
規約：充填の射そのものは V の後合成。
使われ方：Goerss–Jardine I §8。比較ホーンの一方の入力。 -/
def pathLift : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (basedPathMap p).right (basedPathSpace E).basepoint
    (pathSimplex p (v := v)) where
  map := V.map ≫ (PointedMapping.loopToPath E).right
  map_comp := by
    have hn := congrArg Under.Hom.right (loopToPath_natural p)
    simp only [Under.comp_right] at hn
    change (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right ≫
      (PointedMapping.loopToPath B).right =
        (PointedMapping.loopToPath E).right ≫ (basedPathMap p).right at hn
    change (V.map ≫ (PointedMapping.loopToPath E).right) ≫ (basedPathMap p).right = _
    rw [Category.assoc, ← hn, ← Category.assoc, V.map_comp]
    rfl
  face_eq j hj := by
    rw [← Category.assoc, V.face_eq j hj, const_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint]

/-- path に含めた loop の充填の終点は全空間の基点で定数。 -/
@[reassoc (attr := simp)]
lemma pathLift_endpoint : (pathLift p V).map ≫ (pathEndpoint E).right = SSet.const E.basepoint := by
  change (V.map ≫ (PointedMapping.loopToPath E).right) ≫ (pathEndpoint E).right = _
  rw [Category.assoc, PointedMapping.loopToPath_endpoint, comp_const]

/-- 概要：loop の連結射の境界を、元の fiber の loop の単体として表示する。
方針：標準基点の境界を既存 loop–fiber 同型の逆で移す。
規約：面の実際の次数は n。
使われ方：Goerss–Jardine I §8。負符号を持つ loop の代表。 -/
def boundaryLoop : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (pointedFiber p)).right.PtSimplex (n)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (pointedFiber p)).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (loopPointedFiberIso p).inv.right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (loopPointedFiberIso p).inv) (_root_.SerrePositivity.KST.Spectra.BoundaryLift.pointedBoundary V)

/-- 概要：fiber の loop の代表を全空間の path へ含めると、pathLift の最後の面。
方針：loop–fiber の逆同型の包含公式を使い、二つの最後の面の等式を比較する。
規約：代表は選び直さない。
使われ方：Goerss–Jardine I §8。比較ホーンの非定数面の実際の同定。 -/
lemma boundaryLoop_path_include :
    (boundaryLoop p V).map ≫ (PointedMapping.loopToPath (pointedFiber p)).right ≫
        (basedPathMap (pointedFiberι p)).right =
      (pathLift p V).boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (basedPathMap p).right
        ((basedPathMap p).right.app _ (basedPathSpace E).basepoint) := by
  have hn := congrArg Under.Hom.right (PointedMapping.loopFiber_toPath p)
  simp only [Under.comp_right] at hn
  change ((_root_.SerrePositivity.KST.Spectra.BoundaryLift.pointedBoundary V).map ≫ (loopPointedFiberIso p).inv.right) ≫ _ ≫ _ = _
  rw [Category.assoc, hn, ← Category.assoc, BoundaryLift.pointedBoundary_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift.boundary_ι]
  rfl

/-- 概要：pathLift の境界を fiber 内の path に戻すと境界 loop の path 表示に等しい。
方針：全空間の path への包含で比較し、厳密な Hom–fiber 同型の一意性を使う。
規約：fiber 内での射の等式。
使われ方：Goerss–Jardine I §8。出力族の面の公式への代入。 -/
lemma boundaryLoop_path :
    (pathLift p V).boundary.map ≫ (PointedMapping.fiberIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p).inv.right =
      (boundaryLoop p V).map ≫ (PointedMapping.loopToPath (pointedFiber p)).right := by
  apply PointedMapping.fiberHom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p
  have he := congrArg Under.Hom.right (PointedMapping.fiberIso_inv_map_ι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p)
  simp only [Under.comp_right] at he
  rw [Category.assoc, he]
  exact (boundaryLoop_path_include p V).symm

end
end SerrePositivity.KST.Spectra.LoopConnectingComparison
