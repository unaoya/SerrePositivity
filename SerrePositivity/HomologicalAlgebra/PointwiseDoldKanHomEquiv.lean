module
public import SerrePositivity.HomologicalAlgebra.DoldKanHomCoefficient
public import SerrePositivity.HomologicalAlgebra.PointwiseNormalizedMoore
public import SerrePositivity.HomologicalAlgebra.DoldKanGammaDiagram
public import Mathlib.CategoryTheory.Adjunction.Whiskering
/-!
概要：図式圏の指定Dold–Kan Hom同値を点ごとの同じ同値へ移す。
方針：指定係数移送を評価関手へ適用し、元のΓ比較の逆を後合成する。
規約：IS-W2 B02の同じ係数移送の証明分割。指定正規化・Γ比較を保持する。
使われ方：HA 1.2.4、元の正規化重みHomを点ごとの自由鎖随伴へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type*) [Category* J] (C : Type*) [Category* C] [Abelian C]
/-- 図式圏での元のHom同値は指定Γ比較の後で点ごとの同じHom同値となる。 -/
theorem pointwiseDoldKanHomEquiv
    (W : SimplicialObject (J ⥤ C)) (K : ChainComplex (J ⥤ C) ℕ)
    (f : (normalizedMooreComplex (J ⥤ C)).obj W ⟶ K) :
    (flipFunctor SimplexCategoryᵒᵖ J C).map
        ((Abelian.DoldKan.equivalence : SimplicialObject (J ⥤ C) ≌
          ChainComplex (J ⥤ C) ℕ).toAdjunction.homEquiv W K f) ≫
      (pointwiseGammaIso J C).inv.app K =
    (Adjunction.whiskerRight J
      (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction).homEquiv
      W.flip (complexOfFunctorsToFunctorToComplex.obj K)
      ((pointwiseMooreIso J C).inv.app W ≫ complexOfFunctorsToFunctorToComplex.map f) := by
  apply NatTrans.ext
  funext j
  let F := (evaluation J C).obj j
  have h := doldKanHomEquiv_map F W K f
  have h' := congrArg (fun t => t ≫ (gammaMapIso F K).inv) h
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  simp only [Adjunction.homEquiv_apply, NatTrans.comp_app,
    Adjunction.whiskerRight_unit_app_app, pointwiseGammaIso, pointwiseMooreIso,
    NatIso.ofComponents_inv_app, Abelian.DoldKan.equivalence_inverse,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app]
  exact h'.symm
end SerrePositivity.HomologicalAlgebra
