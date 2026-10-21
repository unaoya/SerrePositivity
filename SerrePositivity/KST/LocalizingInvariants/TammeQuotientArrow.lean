module

public import SerrePositivity.KST.LocalizingInvariants.ArrowEssentialSurjectivity
public import SerrePositivity.KST.LocalizingInvariants.TammeQuotientFractions
public import SerrePositivity.KST.LocalizingInvariants.LocalizationEssentialSurjectivity

/-!
概要：一般 Tamme 商への矢印図式の射影は本質的に全射である。
方針：分母を同値とする実四角形で像内の辺を持ち上げ、対象の同型で任意の端点へ移す。
規約：同型は関手 ∞ 圏内に構成する。完全忠実性や有限図式全体の局所化は未主張。
使われ方：商上の fiber・cofiber 図式の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma tammeQuotient_arrow_lift {x y : (laxCategory p q).obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj (tammeQuotient p q))
      ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌) x)
      ((tammeQuotientMap p q).app (Opposite.op ⦋0⦌) y)) :
    ∃ g : (Δ[1] : SSet.{u}) ⟶ (laxCategory p q).obj,
      Nonempty (FunctorIso (g ≫ tammeQuotientMap p q) (SSet.yonedaEquiv.symm f.edge)) := by
  obtain ⟨a, s, g, hs, ⟨c⟩⟩ := tammeQuotient_edge_fraction p q f
  let F := tammeQuotientMap p q
  let sm := s.map ((truncation 2).map F)
  let gm := g.map ((truncation 2).map F)
  let i := Truncated.Edge.id (X := (truncation 2).obj (tammeQuotient p q))
    (F.app (Opposite.op ⦋0⦌) y)
  have hsm : IsInvertibleEdge sm :=
    (isInvertibleEdge_congr (e := (edgeOfSimplex s.edge).map ((truncation 2).map F))
      (f := sm) rfl).mp ((tammeQuotient_isLocalization p q).choose hs)
  have hi : IsInvertibleEdge i := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (Truncated.Edge.id _))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have h : SSet.Truncated.HomotopyCategory.homMk gm ≫
        SSet.Truncated.HomotopyCategory.homMk i =
      SSet.Truncated.HomotopyCategory.homMk sm ≫ SSet.Truncated.HomotopyCategory.homMk f := by
    have hi' : SSet.Truncated.HomotopyCategory.homMk i = 𝟙 _ :=
      SSet.Truncated.HomotopyCategory.homMk_id _
    rw [hi']
    exact (Category.comp_id (obj := hoFunctor.obj (tammeQuotient p q))
      (SSet.Truncated.HomotopyCategory.homMk gm)).trans
        (SSet.Truncated.HomotopyCategory.homMk_comp_homMk c).symm
  obtain ⟨e⟩ := arrowFunctorIso_of_homMk_comm gm f sm i hsm hi h
  refine ⟨SSet.yonedaEquiv.symm g.edge, ⟨?_⟩⟩
  have hg : SSet.yonedaEquiv.symm gm.edge = SSet.yonedaEquiv.symm g.edge ≫ F := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  rw [hg] at e
  exact e

lemma tammeQuotientArrow_isEssentiallySurjective :
    IsEssentiallySurjective ((ihom (Δ[1] : SSet.{u})).map (tammeQuotientMap p q)) :=
  arrowMap_isEssentiallySurjective _
    (localization_isEssentiallySurjective _ _ (tammeQuotient_isLocalization p q))
    (fun f => tammeQuotient_arrow_lift p q f)

end SerrePositivity.KST.LocalizingInvariants
