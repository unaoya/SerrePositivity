module
public import SerrePositivity.KST.SConstruction.BoundaryReduction
public import SerrePositivity.KST.SConstruction.ReductionPointedComparison

/-! # 全零境界の商への点つき π_* 比較
概要：任意の頂点を基点とした反復実現は全零境界の商と同じホモトピー群を持つ。
方針：零次数では全頂点が境界に入り、商の局所化可逆性を点つき Kan 置換へ移す。
規約：実現や境界の Kan 性は不要。使われ方：反復実現の基点の選択の除去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

local instance (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right := Spectra.loopSpace_kanComplex Y

/-- 概要：零次数の添字上では零方向の自己射は恒等。
方針：[0] の自己射の一意性を各座標で使う。
規約：零方向集合は任意。使われ方：全頂点の境界への所属。 -/
lemma zeroDirectionsIndexEndomorphism_zero {r : ℕ} (s : Finset (Fin r)) :
    zeroDirectionsIndexEndomorphism s (fun _ => Opposite.op ⦋0⦌) = 𝟙 _ := by
  funext i
  apply Quiver.Hom.unop_inj
  exact Subsingleton.elim _ _

/-- 概要：任意の頂点は全ての零方向の像に属する。
方針：零次数での自己射が恒等なので全頂点が固定される。
規約：方向集合が空でも成り立つ。使われ方：境界の商への基点比較。 -/
lemma vertex_mem_zeroDirectionsRange {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction r X) _⦋0⦌) :
    x ∈ (zeroDirectionsRange s X).obj (Opposite.op ⦋0⦌) := by
  apply (mem_zeroDirectionsRange_iff s X _ x).2
  rw [zeroDirectionsOperator_eq_map, zeroDirectionsIndexEndomorphism_zero,
    CategoryTheory.Functor.map_id]
  rfl

/-- 概要：正の反復実現の全頂点が全零方向の境界に属する。
方針：第零方向の像への所属を有限合併へ移す。
規約：反復数は r+1。使われ方：任意の基点からの点つき商写像。 -/
lemma vertex_mem_zeroDirectionsFatBoundary (r : ℕ) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction (r + 1) X) _⦋0⦌) :
    x ∈ (zeroDirectionsFatBoundary (r + 1) X).obj (Opposite.op ⦋0⦌) := by
  have h : zeroDirectionsRange (insert (0 : Fin (r + 1)) ∅) X ≤
      zeroDirectionsFatBoundary (r + 1) X :=
    Finset.le_sup (f := fun i => zeroDirectionsRange (insert i ∅) X) (Finset.mem_univ 0)
  exact h _ (vertex_mem_zeroDirectionsRange _ X x)

/-- 概要：部分複体の頂点を基点とした対象から cofiber への点つき写像。
方針：頂点の定値射と cofiber の関係式を合成する。
規約：単射性・可縮性は写像の定義には不要。使われ方：全境界の商への比較。 -/
def cofiberPointedProjection {A B : SSet.{u}} (i : A ⟶ B) (a : A _⦋0⦌) :
    PointedSimplicialSet.ofVertex B (i.app (Opposite.op ⦋0⦌) a) ⟶ PointedObject.cofiber i :=
  Under.homMk (PointedObject.cofiberQuotient i) (by
    change SSet.const (i.app (Opposite.op ⦋0⦌) a) ≫ PointedObject.cofiberQuotient i =
      (PointedObject.cofiber i).hom
    rw [← SSet.const_comp a i, Category.assoc, PointedObject.cofiberQuotient_condition,
      comp_toUnit_assoc, toUnit_unit, Category.id_comp])

/-- 概要：任意の頂点を基点とした反復実現から全境界の商への点つき写像。
方針：頂点が境界に属することを使い cofiber の点つき射影を作る。
規約：基点の選択以外の補完データは不要。使われ方：旧実現の比較。 -/
def boundaryReductionPointedMap (r : ℕ) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction (r + 1) X) _⦋0⦌) :
    PointedSimplicialSet.ofVertex (multiDiagonalCoreSConstruction (r + 1) X) x ⟶
      boundaryReducedRealization r X :=
  cofiberPointedProjection (zeroDirectionsFatBoundary (r + 1) X).ι
    ⟨x, vertex_mem_zeroDirectionsFatBoundary r X x⟩

/-- 概要：全境界の商への点つき比較は Kan 置換後に全基点 π_* 同型。
方針：商写像の局所化可逆性を L9 の実際のホモトピー群へ移す。
規約：零次数を含む全次数。使われ方：基点を選んだ模型との比較。 -/
lemma boundaryReductionPointedMap_kan_piIsomorphism (r : ℕ) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction (r + 1) X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (Spectra.PointedKanReplacement.map (boundaryReductionPointedMap r X x)).right := by
  apply pointedKanReplacement_map_piIsomorphism_of_localized_isIso
  exact boundaryReductionQuotient_image_isIso AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) r X

/-- 概要：全境界を潰す点つき比較に Kan 置換と Ω を適用する。
方針：L9 の円からの点つき内部 Hom を使う。
規約：Ω の座標は L9 の規約。使われ方：反復の loop 模型の比較。 -/
def boundaryReductionLoopMap (r : ℕ) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction (r + 1) X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Spectra.PointedKanReplacement.obj
      (PointedSimplicialSet.ofVertex (multiDiagonalCoreSConstruction (r + 1) X) x)) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((boundaryKanRealizationFunctor r).obj X) :=
  (PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).map
    (Spectra.PointedKanReplacement.map (boundaryReductionPointedMap r X x))

/-- 概要：全境界の商への比較は Ω 後も全基点 π_* 同型。
方針：Kan な点つき対象間の π_* 同型を点つき内部 Hom へ移す。
規約：全次数・全基点を含む。使われ方：K 空間の全境界商模型との比較。 -/
lemma boundaryReductionLoopMap_piIsomorphism (r : ℕ) (X : StableModel.{u})
    (x : (multiDiagonalCoreSConstruction (r + 1) X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (boundaryReductionLoopMap r X x).right :=
  Spectra.PointedMapping.post_piIsomorphism PointedSimplicialSet.circle
    (Spectra.PointedKanReplacement.map (boundaryReductionPointedMap r X x))
    (boundaryReductionPointedMap_kan_piIsomorphism r X x)

end SerrePositivity.KST.SConstruction
