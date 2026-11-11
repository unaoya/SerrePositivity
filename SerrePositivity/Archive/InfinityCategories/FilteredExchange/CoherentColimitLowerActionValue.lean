module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerAction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：下面作用比較の指定値を、元の fiber 族比較の一点成分へ戻す。
方針：始終点の頂点表示の等式輸送を除き、元の成分を保持する。
規約：元の区間輸送を選び直さない。使われ方：下面の三角形比較と共役因子の分離。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 下面作用の元の指定比較は、同じ fiber 族比較の元の成分の指定値に一致する。 -/
lemma coherentColimitLowerActionIso_heq_component :
    HEq (coherentColimitLowerActionIso B H)
      (((coherentColimitLowerFiberHomIso B H).postcomp
        ((ihom (leftUnstraightening F)).map
          (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom)).app
            (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) := by
  unfold coherentColimitLowerActionIso
  dsimp only [_root_.id]
  have hcast {α β : Sort _} (h : α = β) (e : α) : HEq (Eq.mp h e) e := by
    cases h
    rfl
  have htarget {D : Type _} [Category D] {a b b' : D} (e : a ≅ b) (h : b = b') :
      HEq (e ≪≫ eqToIso h) e := by
    subst b'
    simp only [eqToIso_refl, Iso.trans_refl]
    rfl
  exact (htarget _ _).trans ((hcast _ _).trans (hcast _ _))

end SerrePositivity.InfinityCategories.F2
