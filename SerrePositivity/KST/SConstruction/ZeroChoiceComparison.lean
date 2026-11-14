module
public import SerrePositivity.KST.SConstruction.RealizationConnected
public import SerrePositivity.KST.SConstruction.PointedPathComparison

/-! # K 空間の零対象の選択の比較
概要：任意の零頂点を実現の基点に取った loop 空間を、共通の Kan 空間から π_* 同型で比較する。
方針：可縮な零段の core の辺を対角と Kan 置換へ送り、自由 path の二端点を評価する。
規約：全基点・全自然数次数の比較。連結スペクトルの delooping は別に証明する。
使われ方：BGT §7 の K 空間の基点の選択独立性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：二つの零図式を対角実現の中で直接結ぶ辺。
方針：零段の可縮性から辺を取り、零段から対角への写像で送る。
規約：零対象は任意の二つの選択。使われ方：基点変更の path。 -/
def diagonalZeroVertexEdge (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (z z' : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) (hz' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z') :
    SSet.Edge (X := diagonalCoreSConstruction C)
      (coreSConstructionZeroVertex 0 z hz) (coreSConstructionZeroVertex 0 z' hz') := by
  let h := coreSConstructionZero_isContractibleKan C
  let e := Classical.choice ((h.isTerminalVertex (coreSConstructionZeroVertex 0 z' hz')).nonempty_edge
    (coreSConstructionZeroVertex 0 z hz))
  have f := (SSet.Edge.ofTruncated e).map (diagonalZeroColumn (simplicialCoreSConstruction C))
  have h0 := diagonalZeroColumn_zero (simplicialCoreSConstruction C)
    (coreSConstructionZeroVertex 0 z hz)
  have h1 := diagonalZeroColumn_zero (simplicialCoreSConstruction C)
    (coreSConstructionZeroVertex 0 z' hz')
  exact h0 ▸ h1 ▸ f

/-- 概要：零頂点の零図式を Kan 置換した実現の頂点へ送る。
方針：対角の零単体へ Kan 置換の単位を適用する。
規約：基礎の Kan 実現は固定する。使われ方：任意の零対象による基点。 -/
def realizationZeroPoint (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : (kanSRealization C).right _⦋0⦌ :=
  (sRealizationToKan C).right.app (Opposite.op ⦋0⦌) (coreSConstructionZeroVertex 0 z hz)

/-- 概要：任意の二つの零対象による実現の基点を辺で結ぶ。
方針：対角の零図式を結ぶ辺を Kan 置換の単位で送る。
規約：同じ Kan 単体集合の中の辺。使われ方：loop 空間の基点比較。 -/
def realizationZeroEdge (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (z z' : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) (hz' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z') :
    SSet.Edge (realizationZeroPoint C z hz) (realizationZeroPoint C z' hz') :=
  (diagonalZeroVertexEdge C z z' hz hz').map (sRealizationToKan C).right

/-- 概要：任意の零対象を基点に選んだ K 空間。
方針：同じ Kan 実現の基点だけを零図式の像に変えて loop を取る。
規約：Kan 置換の基礎単体集合は変更しない。使われ方：零対象の選択の比較。 -/
def kSpaceAtZero (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : PointedSimplicialSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedSimplicialSet.ofVertex (kanSRealization C).right
    (realizationZeroPoint C z hz))

/-- 概要：任意の零対象を使った K 空間も Kan。
方針：基点を変更した Kan 実現の loop の Kan 性を使う。
規約：基点の選択には依存しない。使われ方：π_* 比較の型条件。 -/
instance kSpaceAtZero_kanComplex (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : KanComplex (kSpaceAtZero C z hz).right :=
  Spectra.loopSpace_kanComplex _

/-- 概要：二つの零対象を使った K 空間は共通の Kan 空間から π_* 同型で比較できる。
方針：実現の基点を結ぶ辺に自由 path による loop 比較を適用する。
規約：π₀ を含む全基点・全次数の比較。使われ方：零対象の選択独立性。 -/
lemma kSpaceAtZero_comparison (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (z z' : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) (hz' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z') :
    ∃ P : Spectra.PointedKanComplex.{u},
      ∃ (f : P.space ⟶ kSpaceAtZero C z hz) (g : P.space ⟶ kSpaceAtZero C z' hz'),
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g.right :=
  exists_loopBasepointComparison (realizationZeroEdge C z z' hz hz')

/-- 概要：任意の点つき単体集合は自身の基点による ofVertex 表示と等しい。
方針：単位からの射と頂点の同値の逆律を使う。
規約：Under の対象の等号。使われ方：標準の K 空間との照合。 -/
lemma ofVertex_basepoint_eq (X : PointedSimplicialSet.{u}) :
    PointedSimplicialSet.ofVertex X.right (PointedSimplicialSet.basepoint X) = X := by
  unfold PointedSimplicialSet.ofVertex PointedSimplicialSet.basepoint
  rw [Equiv.symm_apply_apply]
  exact (StructuredArrow.eq_mk X).symm

/-- 概要：既定の零対象の像は Kan 実現の既定の基点。
方針：Kan 置換の単位が点つき射であることを零次元で評価する。
規約：頂点の厳密等号。使われ方：標準 K 空間との一致。 -/
lemma realizationZeroPoint_chosen (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    realizationZeroPoint C (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).vertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).isZero =
      PointedSimplicialSet.basepoint (kanSRealization C) := by
  have h : (sRealizationToKan C).right.app (Opposite.op ⦋0⦌)
      (PointedSimplicialSet.basepoint (pointedSRealization C)) =
        PointedSimplicialSet.basepoint (kanSRealization C) :=
    congrArg (fun k : 𝟙_ SSet.{u} ⟶ (kanSRealization C).right =>
      k.app (Opposite.op ⦋0⦌) PUnit.unit) (Under.w (sRealizationToKan C))
  simpa only [realizationZeroPoint, pointedSRealization, PointedSimplicialSet.basepoint_ofVertex] using h

/-- 概要：既定の零対象による K 空間は元の kSpace と厳密に一致。
方針：基点の等号と ofVertex 表示の逆律を使う。
規約：点つき対象の等号。使われ方：選択比較と公開 K 空間の接続。 -/
lemma kSpaceAtZero_chosen (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    kSpaceAtZero C (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).vertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).isZero = kSpace C := by
  unfold kSpaceAtZero kSpace
  rw [realizationZeroPoint_chosen, ofVertex_basepoint_eq]

/-- 概要：公開 K 空間と任意の零対象を使った K 空間は π_* 同型の zigzag で比較できる。
方針：既定の零対象と指定した零対象の比較を元の kSpace へ移す。
規約：連結スペクトルの構造射との整合性は後続工程。使われ方：K 空間の基点の選択独立性。 -/
lemma kSpace_zeroChoice_comparison (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    ∃ P : Spectra.PointedKanComplex.{u},
      ∃ (f : P.space ⟶ kSpace C) (g : P.space ⟶ kSpaceAtZero C z hz),
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g.right := by
  exact kanComparison_congr_left (kSpaceAtZero_chosen C)
    (kSpaceAtZero_comparison C _ z (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).isZero hz)

end SerrePositivity.KST.SConstruction
