module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceRho
public import SerrePositivity.KST.LocalizingInvariants.AdjunctInverseFormula

/-!
概要：差の随伴単位の D 成分を、元の cofiber 四角形の右辺から構成する。
方針：右辺の全単体族を実ホモトピーへ戻し、q の実随伴の h Fun 対応で転置する。
規約：lax pullback 内の単位への貼り合わせは後続。使われ方：ρ の実随伴単位。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

/-- 元の普遍 cofiber 四角形の右辺 q(d) → difference(c,d,g) の実ホモトピー。 -/
def laxDifferenceProjectionHomotopy :
    SSet.Homotopy ((laxSnd p q).hom ≫ q.hom) (laxDifference p q) where
  h := (β_ (laxCategory p q).obj (Δ[1] : SSet.{u})).hom ≫
    uncurry (CofiberDiagrams.lift E.obj (F2.laxPullbackArrow p.hom q.hom) ≫
      CofiberDiagrams.right E.obj)
  h₀ := by
    rw [← Category.assoc]
    change prismEndpoint 0 (laxCategory p q).obj ≫ uncurry _ = _
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry, Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Stable.Exact.cofiber_bottom_target_eq_right_source, ← Category.assoc, CofiberDiagrams.lift_bottom]
    exact F2.laxPullbackArrow_target p.hom q.hom
  h₁ := by
    rw [← Category.assoc]
    change prismEndpoint 1 (laxCategory p q).obj ≫ uncurry _ = _
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry, CofiberDiagrams.lift_right_target]
    rfl
  rel := by ext n ⟨x, y⟩; exact x.property.elim

/-- cofiber 射の全族が表す元の h Fun の射。 -/
def laxDifferenceProjectionHom :
    FunctorHom ((laxSnd p q).hom ≫ q.hom) (laxDifference p q) :=
  Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (laxDifferenceProjectionHomotopy p q))

/-- q の随伴による転置。これは D 成分だけで、lax pullback 内の単位ではない。 -/
def laxDifferenceUnitD {v : E.obj ⟶ D.obj} (a : QCatAdjunction q.hom v) :
    FunctorHom (laxSnd p q).hom (laxDifference p q ≫ v) :=
  a.homEquiv (laxSnd p q).hom (laxDifference p q) (laxDifferenceProjectionHom p q)

lemma laxDifferenceUnitD_inverse {v : E.obj ⟶ D.obj} (a : QCatAdjunction q.hom v) :
    (a.homEquiv (laxSnd p q).hom (laxDifference p q)).symm (laxDifferenceUnitD p q a) =
      laxDifferenceProjectionHom p q :=
  Equiv.symm_apply_apply _ _

/-- D 成分を q で写して実余単位を続けると、元の cofiber 射に一致する。 -/
lemma laxDifferenceUnitD_counit {v : E.obj ⟶ D.obj} (a : QCatAdjunction q.hom v) :
    (hoFunctor.map ((ihom (laxCategory p q).obj).map q.hom)).toFunctor.map
        (laxDifferenceUnitD p q a) ≫
      (hoFunctor.map ((pre (laxDifference p q)).app E.obj)).toFunctor.map a.counitHom =
        laxDifferenceProjectionHom p q :=
  (adjunctInverseHomFormula a (laxSnd p q).hom (laxDifference p q)
    (laxDifferenceUnitD p q a)).symm.trans (laxDifferenceUnitD_inverse p q a)

end SerrePositivity.KST.LocalizingInvariants
