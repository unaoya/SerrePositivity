module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanRightCompositionTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：元の coherent 合成四角形の全右 Hom 比較は、任意の全係数制限でも値を保持する。
方針：元の二 Hom 全体の指定比較の前合成へ戻し、同じ二段の前合成を合わせる。
規約：元の合成四角形と指定比較を保つ。使われ方：右 Hom の値比較の全族自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (K L M : KanObject.{u}) {P Q : SSet.{u + 1}}
  (v : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌)
  (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M))
local notation "H₀₁" => Functor.obj SSet.uliftFunctor (SimplicialCategory.sHom K L)
local notation "H₁₂" => Functor.obj SSet.uliftFunctor (SimplicialCategory.sHom L M)
local notation "E" => coherentKanRightCompositionTransportIso K L M
  (SSet.const v : H₀₁ ⊗ H₁₂ ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K))

/-- 元の全係数での合成比較は、同じ元の二 Hom 全体の比較の指定前合成である。 -/
lemma coherentKanRightCompositionTransport_diagonalIso_heq_precomp :
    HEq (coherentKanRightCompositionTransport_diagonalIso K L M v x y)
      (FunctorIso.precomp E (lift x y)) := by
  unfold coherentKanRightCompositionTransport_diagonalIso
  simp only [Eq.mp, Eq.mpr, eqRec_heq_iff]
  rfl

/-- 元の同じ合成四角形の指定比較は、任意の二段の全係数制限でも厳密に値を保つ。 -/
lemma coherentKanRightCompositionTransport_diagonalIso_precomp_heq (r : Q ⟶ P) :
    HEq ((coherentKanRightCompositionTransport_diagonalIso K L M v x y).precomp r)
      (coherentKanRightCompositionTransport_diagonalIso K L M v (r ≫ x) (r ≫ y)) := by
  have h := functorIso_precomp_heq_of_heq (FunctorIso.precomp E (lift x y))
    (coherentKanRightCompositionTransport_diagonalIso K L M v x y)
    (by simp only [diagonalFiberTransport_precomp, SSet.comp_const,
      ← Category.assoc, lift_fst, lift_snd])
    (by simp only [diagonalFiberTransport_precomp, SSet.comp_const, ← Category.assoc])
    (coherentKanRightCompositionTransport_diagonalIso_heq_precomp K L M v x y) r
  have hm := functorIso_precomp_heq_of_map_eq E
    (show r ≫ lift x y = lift (r ≫ x) (r ≫ y) from by apply SSet.hom_ext; intro n; rfl)
  exact h.trans ((heq_of_eq (functorIso_precomp_precomp E (lift x y) r)).trans
    (hm.trans (coherentKanRightCompositionTransport_diagonalIso_heq_precomp
      K L M v (r ≫ x) (r ≫ y)).symm))

end SerrePositivity.InfinityCategories.F2
