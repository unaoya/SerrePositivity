module

public import SerrePositivity.KST.Spectra.PointedBasedIntervalTraces
public import SerrePositivity.KST.Spectra.PointedRelativeTransposeHomotopy
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated

/-!
概要：元の二つの基点固定区間を、同じ合成三角形を保持して貼り合わせる。
方針：内部 Hom の二次元ホーンを充填し、その対角辺を元の区間として読む。
規約：区間の類だけに降ろさない。使われ方：列の厳密化で保持する構造三角形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 元の二つの区間と、その対角区間を持つ実際の合成三角形。 -/
structure BasedPathComposite {T E : PointedSimplicialSet.{u}} {f g h : T ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g)
    (Q : VerticalPath (PointedObject.toPoint E) g h) where
  path : VerticalPath (PointedObject.toPoint E) f h
  triangle : SSet.Edge.CompStruct P.edge Q.edge path.edge

/-- 同じ内部 Hom のホーン充填から、実三角形を保つ合成区間を選ぶ。 -/
def BasedPathComposite.choose {T E : PointedSimplicialSet.{u}} [KanComplex E.right]
    {f g h : T ⟶ E} (P : VerticalPath (PointedObject.toPoint E) f g)
    (Q : VerticalPath (PointedObject.toPoint E) g h) : BasedPathComposite P Q := by
  let homKan : KanComplex (PointedObject.basedHom T E).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let d := P.edge.toTruncated.comp Q.edge.toTruncated
  refine ⟨basedPathOfEdge (SSet.Edge.ofTruncated d), ?_⟩
  rw [basedPathOfEdge_edge]
  exact SSet.Edge.CompStruct.ofTruncated (P.edge.toTruncated.compStruct Q.edge.toTruncated)

namespace VerticalPath

/-- ホモトピーから内部 Hom へ移して評価しても、入力した同じ区間に戻る。 -/
lemma ofHomotopy_h {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g : T ⟶ E}
    (H : SSet.Homotopy f.right g.right)
    (hb : T.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom)
    (hp : H.h ≫ p.right = fst T.right (Δ[1] : SSet.{u}) ≫ f.right ≫ p.right) :
    (ofHomotopy H hb hp).homotopy.h = H.h := by
  rw [homotopy_h]
  change uncurry (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry T E H.h hb ≫ _) = _
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, uncurry_curry]

/-- 評価した全区間が一致すれば、内部 Hom の同じ区間族も一致する。 -/
lemma path_eq_of_homotopy_h_eq {T E B C : PointedSimplicialSet.{u}}
    {p : E ⟶ B} {q : E ⟶ C} {f g f' g' : T ⟶ E}
    (P : VerticalPath p f g) (Q : VerticalPath q f' g')
    (h : P.homotopy.h = Q.homotopy.h) : P.path = Q.path := by
  apply (cancel_mono (PointedObject.basedHomι T E)).1
  apply uncurry_injective
  simpa only [← homotopy_h] using h

end VerticalPath
end SerrePositivity.KST.Spectra.PointedMapping
