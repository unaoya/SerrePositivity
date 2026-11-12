module

public import SerrePositivity.KST.Spectra.PointedPathSquareReflection

/-!
概要：端点を別の射で表示した二つの元の区間へ、同じ像の正方形を境界固定で反映する。
方針：区間そのものは変えず、端点の等式から境界の一致を証明して相対持ち上げする。
規約：同じ元の辺と基底正方形へのトレースを保持する。使われ方：交換自然性の具体的適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

variable {T E : PointedSimplicialSet.{u}} {f g f' g' : T ⟶ E}
  (P : VerticalPath (PointedObject.toPoint E) f g)
  (Q : VerticalPath (PointedObject.toPoint E) f' g') (hf : f = f') (hg : g = g')

include hf hg in
/-- 元の二辺を変えず、端点の厳密な等式から境界全体の一致を得る。 -/
lemma pathBoundary_eq_of_endpoints :
    (boundary 1).ι ≫ P.path = (boundary 1).ι ≫ Q.path := by
  cases hf
  cases hg
  exact pathBoundary_eq P Q

/-- 端点が別表示の元の二辺に、同じ一定な境界ホモトピーを指定する。 -/
def pathEndpointBoundaryHomotopy :
    SSet.Homotopy ((boundary 1).ι ≫ P.path) ((boundary 1).ι ≫ Q.path) where
  h := fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path
  h₀ := by rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]; rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    exact pathBoundary_eq_of_endpoints P Q hf hg
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 指定した全境界は、同じ一定正方形の制限そのもの。 -/
lemma pathEndpointBoundaryHomotopy_h : (pathEndpointBoundaryHomotopy P Q hf hg).h =
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ P.constantSquare.h := by
  change fst _ _ ≫ (boundary 1).ι ≫ P.path =
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ (fst _ _ ≫ P.path)
  rw [whiskerRight_fst_assoc]

variable {B : PointedSimplicialSet.{u}} [KanComplex E.right] [KanComplex B.right]
  (q : E ⟶ B) (hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism q.right)
  (H : SSet.Homotopy ((P.basedPost q).path) ((Q.basedPost q).path))
  (hH₀ : SquareAdjustment.leftSide ≫ H.h = SSet.const (familyVertex (f ≫ q)))
  (hH₁ : SquareAdjustment.rightSide ≫ H.h = SSet.const (familyVertex (g ≫ q)))

/-- 元の二辺を表示し直さず、端点の等式を別に保持して像の比較を反映する。 -/
def pathEndpointSquareReflection :
    RelativeHomotopyReflection (PointedObject.basedHomMap T q) (boundary 1).ι H
      (pathEndpointBoundaryHomotopy P Q hf hg) := by
  let homE : KanComplex (PointedObject.basedHom T E).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let homB : KanComplex (PointedObject.basedHom T B).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  have hv : (pathEndpointBoundaryHomotopy P Q hf hg).h ≫
      (PointedObject.basedHomMap T q).right = (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h := by
    rw [pathEndpointBoundaryHomotopy_h, Category.assoc]
    change (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ (P.basedPost q).constantSquare.h = _
    rw [SquareAdjustment.boundary_restriction, SquareAdjustment.boundary_restriction,
      (P.basedPost q).constantSquare_start, (P.basedPost q).constantSquare_finish, hH₀, hH₁]
  exact RelativeHomotopyReflection.choose (PointedObject.basedHomMap T q)
    (post_piIsomorphism T q hq) (boundary 1).ι H
    (pathEndpointBoundaryHomotopy P Q hf hg) hv

/-- 端点の表示を保持して反映した実正方形も、元の端点の全境界で一定。 -/
lemma pathEndpointSquareReflection_boundary :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫
        (pathEndpointSquareReflection P Q hf hg q hq H hH₀ hH₁).homotopy.h =
      intervalBoundaryFamily (SSet.const (familyVertex f)) (SSet.const (familyVertex g)) := by
  have hb := (pathEndpointSquareReflection P Q hf hg q hq H hH₀ hH₁).homotopy_relative
  rw [pathEndpointBoundaryHomotopy_h] at hb
  rw [SquareAdjustment.boundary_restriction P.constantSquare.h,
    P.constantSquare_start, P.constantSquare_finish] at hb
  exact hb

end SerrePositivity.KST.Spectra.PointedMapping
