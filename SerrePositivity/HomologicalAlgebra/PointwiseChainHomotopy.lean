module
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
概要：各対象で指定した自然な鎖ホモトピーを、図式圏の一つの鎖ホモトピーに組み立てる。
方針：次数を一つ上げる成分の自然性を使い、他の成分は元の零条件で処理する。
規約：元の鎖写像と各点のホモトピー成分を変更しない。
使われ方：HA 1.2.4、G10 の自然な EZ 比較を図式圏で係数変更・延長する入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {J C : Type*} [Category* J] [Category* C] [Preadditive C]
variable {K L : ChainComplex (J ⥤ C) ℕ} {f g : K ⟶ L}

/-- 次数を一つ上げる成分の自然性から、元の各点のホモトピーを図式圏へまとめる。 -/
def pointwiseChainHomotopy
    (h : ∀ a : J, Homotopy
      ((((evaluation J C).obj a).mapHomologicalComplex (.down ℕ)).map f)
      ((((evaluation J C).obj a).mapHomologicalComplex (.down ℕ)).map g))
    (hn : ∀ {a b : J} (t : a ⟶ b) (i : ℕ),
      (K.X i).map t ≫ (h b).hom i (i + 1) =
        (h a).hom i (i + 1) ≫ (L.X (i + 1)).map t) : Homotopy f g where
  hom i j := {
    app a := (h a).hom i j
    naturality := by
      intro a b t
      by_cases hij : j = i + 1
      · subst j
        exact hn t i
      · have hr : ¬ (ComplexShape.down ℕ).Rel j i := fun hh => hij hh.symm
        rw [(h a).zero i j hr, (h b).zero i j hr, comp_zero, zero_comp] }
  zero i j hij := by
    apply NatTrans.ext
    funext a
    exact (h a).zero i j hij
  comm i := by
    apply NatTrans.ext
    funext a
    exact (h a).comm i

/-- 得られたホモトピーの各点の成分は指定した成分そのもの。 -/
theorem pointwiseChainHomotopy_hom_app
    (h : ∀ a : J, Homotopy
      ((((evaluation J C).obj a).mapHomologicalComplex (.down ℕ)).map f)
      ((((evaluation J C).obj a).mapHomologicalComplex (.down ℕ)).map g))
    (hn : ∀ {a b : J} (t : a ⟶ b) (i : ℕ),
      (K.X i).map t ≫ (h b).hom i (i + 1) =
        (h a).hom i (i + 1) ≫ (L.X (i + 1)).map t)
    (i j : ℕ) (a : J) : ((pointwiseChainHomotopy h hn).hom i j).app a = (h a).hom i j := rfl

end SerrePositivity.HomologicalAlgebra
