module

public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-!
概要：点つき射の垂直なホモトピーを、元の内部 Hom の区間族として記録する。
方針：端点を元の定数族で指定し、射影後の区間全体が定数であることを保持する。
規約：Kan 性不要。使われ方：指定した部分パラメータを固定する列の相対厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 任意のパラメータで一定の Hom の頂点を評価すると、元の同じ点つき射になる。 -/
lemma uncurry_const_familyVertex {T E : PointedSimplicialSet.{u}} (f : T ⟶ E)
    (A : SSet.{u}) :
    uncurry ((SSet.const (X := A) (familyVertex f)) ≫ PointedObject.basedHomι T E) =
      fst T.right A ≫ f.right := by
  let k : A ⟶ (Δ[0] : SSet.{u}) := SSet.const (stdSimplex.obj₀Equiv.symm 0)
  have hk : k ≫ pointFamily f = SSet.const (X := A) (familyVertex f) := by
    rw [SSet.const_comp]
    have hv : stdSimplex.obj₀Equiv.symm 0 =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply stdSimplex.ext
      intro j
      apply Fin.ext
      omega
    rw [hv, ← SSet.yonedaEquiv_comp, Category.id_comp]
    rfl
  rw [← hk, Category.assoc, pointFamily, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι,
    uncurry_natural_left, uncurry_curry]
  rfl

/-- 点つき内部 Hom に値を取り、射影後の全区間が元の始点で一定の区間族。 -/
structure VerticalPath {T E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (f g : T ⟶ E) where
  path : (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom T E).right
  zero : stdSimplex.δ (1 : Fin 2) ≫ path = pointFamily f
  one : stdSimplex.δ (0 : Fin 2) ≫ path = pointFamily g
  over : path ≫ (PointedObject.basedHomMap T p).right =
    SSet.const (familyVertex (f ≫ p))

namespace VerticalPath
variable {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g : T ⟶ E}

/-- 垂直区間族は、元の点つき内部 Hom の同じ端点を結ぶ辺。 -/
def edge (H : VerticalPath p f g) :
    (PointedObject.basedHom T E).right.Edge (familyVertex f) (familyVertex g) :=
  SSet.Edge.mk (SSet.yonedaEquiv H.path)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, H.zero]; rfl)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, H.one]; rfl)

/-- 垂直区間族が与える元の点つき射の実際のホモトピー。 -/
def homotopy (H : VerticalPath p f g) : SSet.Homotopy f.right g.right := homotopyOfEdge H.edge

/-- 垂直区間族を評価したホモトピーの全区間の射。 -/
lemma homotopy_h (H : VerticalPath p f g) :
    H.homotopy.h = uncurry (H.path ≫ PointedObject.basedHomι T E) := by
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv H.path) ≫ _) = _
  rw [Equiv.symm_apply_apply]

/-- 評価したホモトピーは基点を全区間で固定する。 -/
lemma homotopy_base (H : VerticalPath p f g) :
    T.hom ▷ (Δ[1] : SSet.{u}) ≫ H.homotopy.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom := homotopyOfEdge_base H.edge

/-- 評価したホモトピーは元の射影を全区間で固定する。 -/
lemma homotopy_over (H : VerticalPath p f g) :
    H.homotopy.h ≫ p.right = fst T.right (Δ[1] : SSet.{u}) ≫ f.right ≫ p.right := by
  rw [homotopy_h, ← uncurry_natural_right, Category.assoc,
    ← PointedObject.basedHomMap_ι, ← Category.assoc, H.over, uncurry_const_familyVertex]
  rfl

/-- 元の点つきホモトピーを、同じ端点・基点・射影を持つ内部 Hom の垂直区間へ移す。 -/
def ofHomotopy (H : SSet.Homotopy f.right g.right)
    (hbase : T.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom)
    (hvertical : H.h ≫ p.right = fst T.right (Δ[1] : SSet.{u}) ≫ f.right ≫ p.right) :
    VerticalPath p f g where
  path := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry T E H.h hbase
  zero := paramCurry_homotopy_zero H hbase
  one := paramCurry_homotopy_one H hbase
  over := by
    apply (cancel_mono (PointedObject.basedHomι T B)).1
    rw [Category.assoc, PointedObject.basedHomMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι,
      ← curry_natural_right]
    apply uncurry_injective
    rw [uncurry_curry, uncurry_const_familyVertex]
    exact hvertical

/-- 垂直区間族の端点は、元の射影へ戻すと厳密に同じ射。 -/
lemma endpoint_over (H : VerticalPath p f g) : g ≫ p = f ≫ p := by
  have h := congrArg (SSet.ι₁ ≫ ·) H.homotopy_over
  rw [← Category.assoc, H.homotopy.h₁] at h
  apply Under.UnderMorphism.ext
  exact h

end VerticalPath

end SerrePositivity.KST.Spectra.PointedMapping
