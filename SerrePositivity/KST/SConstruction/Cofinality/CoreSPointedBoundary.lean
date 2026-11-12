module
public import SerrePositivity.KST.SConstruction.Cofinality.SingleRealizationBoundary
public import SerrePositivity.KST.Spectra.KanCompositeCancellation

/-!
概要：元の core S 実現の任意頂点を基点にし、同じ境界商への比較を保つ。
方針：指定射の実像を標的基点とし、元の商の自然性を点つきにする。
規約：chosen zero の厳密保存を追加仮定にしない。
使われ方：元の Ex∞ 包含の群条件を境界 Kan 模型へ移す。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories

open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：元の core S 実現の指定頂点を基点とする同じ対象。
方針：既存の頂点からの点つき対象を包む。
規約：零対象の選択に制約を付けない。
使われ方：同じ Ex∞ の点つき比較。 -/
def coreSVertexObject (X : StableModel.{u})
    (x : (coreSRealizationFunctor.obj X) _⦋0⦌) : PointedSSetObject.{u} :=
  ⟨PointedSimplicialSet.ofVertex (coreSRealizationFunctor.obj X) x⟩

/-- 概要：元の完全射の実像を基点とする元の点つき実現射。
方針：頂点の像への標準点つき射を使う。
規約：元の基礎射を変更しない。
使われ方：基点の厳密保存を持つ境界比較の四角形。 -/
def coreSVertexMap {X Y : StableModel.{u}} (f : X ⟶ Y)
    (x : (coreSRealizationFunctor.obj X) _⦋0⦌) :
    coreSVertexObject X x ⟶ coreSVertexObject Y
      ((coreSRealizationFunctor.map f).app (Opposite.op ⦋0⦌) x) :=
  Spectra.pointedMapAtVertex (coreSRealizationFunctor.map f) x

/-- 概要：元の core S 実現の任意頂点から元の境界商への点つき射。
方針：同じ境界商の全頂点の回収を使う。
規約：元の商の基点を保持する。
使われ方：同じ元の SOA と Ex∞ の比較。 -/
def coreSVertexBoundary (X : StableModel.{u})
    (x : (coreSRealizationFunctor.obj X) _⦋0⦌) :
    (coreSVertexObject X x).obj ⟶ (boundaryReducedRealizationFunctor 0).obj X :=
  boundaryReductionPointedMap 0 X x

/-- 概要：元の点つき実現射と境界商の四角形は厳密に可換。
方針：元の基礎射の商の自然性を使う。
規約：指定射の像を標的基点にする。
使われ方：Kan 置換後の同じ誘導写像の照合。 -/
lemma coreSVertexBoundary_naturality {X Y : StableModel.{u}} (f : X ⟶ Y)
    (x : (coreSRealizationFunctor.obj X) _⦋0⦌) :
    coreSVertexMap f x ≫ coreSVertexBoundary Y
        ((coreSRealizationFunctor.map f).app (Opposite.op ⦋0⦌) x) =
      coreSVertexBoundary X x ≫ (boundaryReducedRealizationFunctor 0).map f := by
  apply Under.UnderMorphism.ext
  exact coreSBoundaryQuotient_naturality f

/-- 概要：同じ Ex∞ の元の境界商比較は全基点 π 同型。
方針：元の商の局所化同型を Ex∞ で保存して Kan 比較へ渡す。
規約：任意の元の頂点で基点を付けた同じ射。
使われ方：元の包含の次数条件を境界 Kan 模型で反映する。 -/
lemma coreSExInfinityBoundary_piIsomorphism (X : StableModel.{u})
    (x : (coreSRealizationFunctor.obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (exInfinityPointedKanMap
      (X := coreSVertexObject X x)
      (Y := ⟨(boundaryReducedRealizationFunctor 0).obj X⟩)
      (coreSVertexBoundary X x)).hom.right := by
  apply kanPiIsomorphism_of_localized_isIso
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff (boundaryReductionQuotient 0 X)).mpr
    (boundaryReductionQuotient_image_isIso AnodyneHomotopy.anodyneQ
      (Localization.inverts _ anodyneExtensions) 0 X)

end SerrePositivity.KST.SConstruction.Cofinality
