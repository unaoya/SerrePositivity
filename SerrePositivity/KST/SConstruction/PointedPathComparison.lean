module
public import SerrePositivity.KST.SConstruction.KSpace
public import SerrePositivity.KST.Spectra.UnpointedPathEvaluation
public import SerrePositivity.KST.Spectra.PostMappingLifts

/-! # 基点を結ぶ辺からの loop 空間の比較
概要：Kan 複体の一つの辺の両端を基点に取った loop 空間は、共通の Kan 空間からの π_* 同型で比較できる。
方針：辺を自由 path 空間の基点に取り、二つの端点評価を点つき射にする。
規約：全基点・全自然数次数の π_* 同型を使う。
使われ方：S• 実現の零対象の選択独立性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：Kan 複体に任意の頂点を基点として付けても基礎単体集合は Kan。
方針：基礎対象が元の X であることを使う。
規約：基点の条件を追加しない。使われ方：基点変更の loop 空間の Kan 性。 -/
instance pointedOfVertex_kanComplex (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    KanComplex (PointedSimplicialSet.ofVertex X x).right := inferInstanceAs (KanComplex X)

/-- 概要：L9 の自由 path の端点評価は関手頂点の通常の評価と一致。
方針：単位の内部 Hom の同型と pre の各成分を計算する。
規約：任意の単体集合。使われ方：辺の端点と点つき評価の照合。 -/
lemma pathEvaluation_eq_evaluateFunctorAt (X : SSet.{u}) (t : Fin 2) :
    Spectra.KanPath.evaluation X t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm t) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 概要：与えた区間図式を自由 path 空間の基点に取る。
方針：関手頂点で点つき単体集合を作る。
規約：端点の基点が異なることを許す。使われ方：基点変更の共通比較対象。 -/
def pointedPathAt {X : SSet.{u}} (p : (Δ[1] : SSet.{u}) ⟶ X) : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.ofVertex (Spectra.KanPath.object X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)

/-- 概要：自由 path の点つき端点評価。
方針：基点の path を評価すると指定された端点になることを使う。
規約：t=0 が始点、t=1 が終点。使われ方：二つの基点での loop の比較。 -/
def pointedPathEndpoint {X : SSet.{u}} (p : (Δ[1] : SSet.{u}) ⟶ X) (t : Fin 2) :
    pointedPathAt p ⟶ PointedSimplicialSet.ofVertex X
      (p.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm t)) :=
  Under.homMk (Spectra.KanPath.evaluation X t) (by
    apply (SSet.unitHomEquiv _).injective
    change (Spectra.KanPath.evaluation X t).app (Opposite.op ⦋0⦌)
      (SSet.unitHomEquiv _ ((SSet.unitHomEquiv _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))) =
        SSet.unitHomEquiv _ ((SSet.unitHomEquiv _).symm
          (p.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm t)))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      pathEvaluation_eq_evaluateFunctorAt, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex])

/-- 概要：Kan 標的の点つき path 対象は Kan。
方針：L9 の自由 path の Kan 性を使う。
規約：基点の位置には依存しない。使われ方：比較の π_* の定義域。 -/
instance pointedPathAt_kanComplex {X : SSet.{u}} [KanComplex X] (p : (Δ[1] : SSet.{u}) ⟶ X) :
    KanComplex (pointedPathAt p).right := Spectra.KanPath.object_kanComplex X

/-- 概要：点つき端点評価は全ての単射に右持ち上げ性を持つ。
方針：L9 の端点評価の充填性を使う。
規約：基礎射への条件。使われ方：loop への指数での充填性。 -/
lemma pointedPathEndpoint_rlp {X : SSet.{u}} [KanComplex X]
    (p : (Δ[1] : SSet.{u}) ⟶ X) (t : Fin 2) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (pointedPathEndpoint p t).right :=
  Spectra.KanPath.evaluation_rlp X t

/-- 概要：点つき端点評価が loop 空間の間に誘導する射。
方針：円を始域とする点つき内部 Hom の後合成を使う。
規約：同じ共通比較対象から両端へ向かう。使われ方：基点変更の zigzag。 -/
def loopPathEndpoint {X : SSet.{u}} (p : (Δ[1] : SSet.{u}) ⟶ X) (t : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (pointedPathAt p) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedSimplicialSet.ofVertex X
        (p.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm t))) :=
  PointedObject.basedHomMap (C := SSet.{u}) PointedSimplicialSet.circle.{u}
    (Y := pointedPathAt p)
    (Z := PointedSimplicialSet.ofVertex X
      (p.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm t))) (pointedPathEndpoint p t)

/-- 概要：loop への端点評価も全ての単射に右持ち上げ性を持つ。
方針：点つき写像空間の後合成の充填性を円に適用する。
規約：基礎射の条件。使われ方：loop 空間の全基点 π_* 比較。 -/
lemma loopPathEndpoint_rlp {X : SSet.{u}} [KanComplex X]
    (p : (Δ[1] : SSet.{u}) ⟶ X) (t : Fin 2) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (loopPathEndpoint p t).right :=
  Spectra.PointedMapping.post_rlp_monomorphisms _ _ (pointedPathEndpoint_rlp p t)

/-- 概要：loop への端点評価は全基点の全次数で π_* 同型。
方針：Kan な両端と全単射 RLP に L9 の一般定理を適用する。
規約：π₀ も含む。使われ方：零対象の選択によらない K 空間の比較。 -/
lemma loopPathEndpoint_piIsomorphism {X : SSet.{u}} [KanComplex X]
    (p : (Δ[1] : SSet.{u}) ⟶ X) (t : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (loopPathEndpoint p t).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (loopPathEndpoint_rlp p t)

/-- 概要：一つの辺で結ばれた二基点の loop 空間は共通の Kan 空間から π_* 同型で比較できる。
方針：辺を path 空間の基点とし、二つの端点評価を loop に移す。
規約：全基点の π₀ を含む全次数。使われ方：零対象の選択独立性。 -/
lemma exists_loopBasepointComparison {X : SSet.{u}} [KanComplex X]
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    ∃ P : Spectra.PointedKanComplex.{u},
      ∃ (f : P.space ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedSimplicialSet.ofVertex X x))
        (g : P.space ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedSimplicialSet.ofVertex X y)),
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g.right := by
  let p : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm e.edge
  have hp0 : p.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = x := by
    have hv : (stdSimplex.obj₀Equiv.symm (0 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
        stdSimplex.objEquiv.symm (SimplexCategory.δ (1 : Fin 2)) := by decide
    dsimp only [p]
    rw [hv, SSet.yonedaEquiv_symm_app_objEquiv_symm]
    exact e.src_eq
  have hp1 : p.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = y := by
    have hv : (stdSimplex.obj₀Equiv.symm (1 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
        stdSimplex.objEquiv.symm (SimplexCategory.δ (0 : Fin 2)) := by decide
    dsimp only [p]
    rw [hv, SSet.yonedaEquiv_symm_app_objEquiv_symm]
    exact e.tgt_eq
  rw [← hp0, ← hp1]
  exact ⟨⟨_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (pointedPathAt p), inferInstance⟩,
    loopPathEndpoint p 0, loopPathEndpoint p 1,
    loopPathEndpoint_piIsomorphism p 0, loopPathEndpoint_piIsomorphism p 1⟩

/-- 概要：共通 Kan 空間からの π_* 比較は左の点つき対象の等号で移せる。
方針：Kan 性の証明も含めて等号を消去する。
規約：対象の等号の移送であり、新しい比較仮定は加えない。
使われ方：既定の零対象の比較を公開 K 空間へ移す。 -/
lemma kanComparison_congr_left {A A' B : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex A'.right] [KanComplex B.right] (h : A = A')
    (hc : ∃ P : Spectra.PointedKanComplex.{u}, ∃ (f : P.space ⟶ A) (g : P.space ⟶ B),
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g.right) :
    ∃ P : Spectra.PointedKanComplex.{u}, ∃ (f : P.space ⟶ A') (g : P.space ⟶ B),
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g.right := by
  subst A'
  exact hc

end SerrePositivity.KST.SConstruction
