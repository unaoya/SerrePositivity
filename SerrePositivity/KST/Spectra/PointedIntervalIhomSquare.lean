module

public import SerrePositivity.KST.Spectra.PointedIhomIntervalNaturality
public import SerrePositivity.KST.Spectra.PointedIntervalInputBoundary

/-!
概要：同じ実正方形と一定境界を、内部 Hom の関手作用へ移す。
方針：同じ二次元射へ ihomAction を後合成し、頂点を評価と curry で計算する。
規約：Kan 性・充填不要。使われ方：交換トレースの全族射影比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 内部 Hom の全族作用は、元の射の頂点を同じ内部 Hom の後合成へ送る。 -/
lemma familyVertex_ihomAction (K : PointedSimplicialSet.{u})
    {A E : PointedSimplicialSet.{u}} (f : A ⟶ E) :
    (ihomAction K A E).right.app _ (familyVertex f) =
      familyVertex (PointedObject.basedHomMap K f) := by
  have he : curry ((ihom.ev K).app A ≫ f) = (ihom K).map f := by
    rw [curry_natural_right, ← uncurry_id_eq_ev, curry_uncurry, Category.id_comp]
  change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K (PointedObject.basedHom K A) E).hom.right.app _
    ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((ihom.ev K).app A) E).right.app _ (familyVertex f)) = _
  rw [familyVertex_pre, ← familyVertex_curry, he]
  rfl

namespace VerticalPath
variable {A E : PointedSimplicialSet.{u}} {f g f' g' : A ⟶ E}
  (R : VerticalPath (PointedObject.toPoint E) f g)
  (T : VerticalPath (PointedObject.toPoint E) f' g')
  (H : SSet.Homotopy R.path T.path) (K : PointedSimplicialSet.{u})

/-- 同じ二次元射へ内部 Hom の作用を施した正方形。 -/
def basedIhomSquare : SSet.Homotopy (R.basedIhomMap K).path (T.basedIhomMap K).path where
  h := H.h ≫ (ihomAction K A E).right
  h₀ := by rw [← Category.assoc, H.h₀, basedIhomMap_path]; rfl
  h₁ := by rw [← Category.assoc, H.h₁, basedIhomMap_path]; rfl
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 一定な指定境界も、同じ内部 Hom の作用による一定境界となる。 -/
lemma basedIhomSquare_side (i : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) (a : A ⟶ E)
    (ha : i ≫ H.h = SSet.const (familyVertex a)) :
    i ≫ (basedIhomSquare R T H K).h =
      SSet.const (familyVertex ((ihom K).map a)) := by
  simp only [PointedObject.ihom_obj_eq_basedHom]
  change i ≫ (H.h ≫ (ihomAction K A E).right) = _
  rw [← Category.assoc, ha, SSet.const_comp, familyVertex_ihomAction]
  rfl

end VerticalPath
end SerrePositivity.KST.Spectra.PointedMapping
