module

public import SerrePositivity.KST.Spectra.RelativeHomotopyReflection
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism
public import SerrePositivity.KST.Spectra.PointedConstantIntervalSquare

/-!
概要：π 同型による像の両端境界固定正方形を、元の実区間同士の正方形へ反映する。
方針：両端境界の一定ホモトピーを指定し、内部 Hom の写像 path に相対持ち上げする。
規約：元の二辺と全境界・基底トレースを保持する。使われ方：交換区間の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

variable {T E : PointedSimplicialSet.{u}} {f g : T ⟶ E}
  (P Q : VerticalPath (PointedObject.toPoint E) f g)

/-- 同じ両端を持つ元の二つの区間の境界全体は厳密に一致する。 -/
lemma pathBoundary_eq : (boundary 1).ι ≫ P.path = (boundary 1).ι ≫ Q.path := by
  apply boundary.hom_ext
  intro j
  rw [← Category.assoc, ← Category.assoc, boundary.ι_ι]
  fin_cases j
  · exact P.one.trans Q.one.symm
  · exact P.zero.trans Q.zero.symm

/-- 元の二辺の同じ端点境界を、全区間で一定に保つ指定ホモトピー。 -/
def pathBoundaryHomotopy :
    SSet.Homotopy ((boundary 1).ι ≫ P.path) ((boundary 1).ι ≫ Q.path) where
  h := fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path
  h₀ := by rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]; rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    exact pathBoundary_eq P Q
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 指定した境界ホモトピーは、元の同じ一定正方形の境界制限そのもの。 -/
lemma pathBoundaryHomotopy_h : (pathBoundaryHomotopy P Q).h =
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ P.constantSquare.h := by
  change fst _ _ ≫ (boundary 1).ι ≫ P.path =
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ (fst _ _ ≫ P.path)
  rw [whiskerRight_fst_assoc]

variable {B : PointedSimplicialSet.{u}} [KanComplex E.right] [KanComplex B.right]
  (q : E ⟶ B) (hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism q.right)
  (H : SSet.Homotopy ((P.basedPost q).path) ((Q.basedPost q).path))
  (hH₀ : SquareAdjustment.leftSide ≫ H.h = SSet.const (familyVertex (f ≫ q)))
  (hH₁ : SquareAdjustment.rightSide ≫ H.h = SSet.const (familyVertex (g ≫ q)))

/-- 元の区間と境界全体、および指定した像の二次元射へのトレースを持つ反映データ。 -/
def pathSquareReflection :
    RelativeHomotopyReflection (PointedObject.basedHomMap T q) (boundary 1).ι H
      (pathBoundaryHomotopy P Q) := by
  let homE : KanComplex (PointedObject.basedHom T E).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  let homB : KanComplex (PointedObject.basedHom T B).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  have hv : (pathBoundaryHomotopy P Q).h ≫ (PointedObject.basedHomMap T q).right =
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h := by
    have hp : (pathBoundaryHomotopy P Q).h ≫ (PointedObject.basedHomMap T q).right =
        (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ (P.basedPost q).constantSquare.h := by
      rw [pathBoundaryHomotopy_h, Category.assoc]
      rfl
    rw [hp, SquareAdjustment.boundary_restriction, SquareAdjustment.boundary_restriction,
      (P.basedPost q).constantSquare_start, (P.basedPost q).constantSquare_finish, hH₀, hH₁]
  exact RelativeHomotopyReflection.choose (PointedObject.basedHomMap T q)
    (post_piIsomorphism T q hq) (boundary 1).ι H (pathBoundaryHomotopy P Q) hv

/-- 反映された実正方形も、元の同じ始点・終点の全境界で一定。 -/
lemma pathSquareReflection_boundary :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫
        (pathSquareReflection P Q q hq H hH₀ hH₁).homotopy.h =
      intervalBoundaryFamily (SSet.const (familyVertex f)) (SSet.const (familyVertex g)) := by
  have hb := (pathSquareReflection P Q q hq H hH₀ hH₁).homotopy_relative
  rw [pathBoundaryHomotopy_h] at hb
  rw [SquareAdjustment.boundary_restriction P.constantSquare.h,
    P.constantSquare_start, P.constantSquare_finish] at hb
  exact hb

/-- 反映された元の正方形の左辺全体は、元の始点の頂点で一定。 -/
lemma pathSquareReflection_start :
    SquareAdjustment.leftSide ≫ (pathSquareReflection P Q q hq H hH₀ hH₁).homotopy.h =
      SSet.const (familyVertex f) :=
  (SquareAdjustment.sides_of_boundary_restriction _
    (pathSquareReflection_boundary P Q q hq H hH₀ hH₁)).1

/-- 反映された元の正方形の右辺全体も、元の終点の頂点で一定。 -/
lemma pathSquareReflection_finish :
    SquareAdjustment.rightSide ≫ (pathSquareReflection P Q q hq H hH₀ hH₁).homotopy.h =
      SSet.const (familyVertex g) :=
  (SquareAdjustment.sides_of_boundary_restriction _
    (pathSquareReflection_boundary P Q q hq H hH₀ hH₁)).2

end SerrePositivity.KST.Spectra.PointedMapping
