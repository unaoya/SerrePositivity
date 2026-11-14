module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGCounitColumnQuasiIso
public import Mathlib.CategoryTheory.Adjunction.Basic
/-!
概要：実 dg 関手の H⁰ 随伴の同じ余単位を、元の dg 圏の実閉射で表す。
方針：右随伴の対象を戻し、閉射の商の全射性と同じ随伴の Hom 同値を使う。
規約：元の対象・全射に対する普遍性を保持。使われ方：余単位による全 Hom の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 同じ実閉余単位は全入力の H⁰ Hom 集合の全単射を与える。 -/
lemma dgHomotopyAdjunction_counit_closed_exists (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (H : _root_.SerrePositivity.DifferentialGraded.HomotopyCategory R E ⥤ _root_.SerrePositivity.DifferentialGraded.HomotopyCategory R C) (adj : G.onHomotopy ⊣ H) (y : E) :
    ∃ (t : C) (ε : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj t) ⟶
        ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y),
      ∀ x : C, Function.Bijective (fun f :
        (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) ⟶
          (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) =>
        G.onHomotopy.map f ≫ (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map ε) := by
  let yH := (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
  let t := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (H.obj yH).as
  have ht : (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t) = H.obj yH := rfl
  let i := eqToIso ht
  let εH := G.onHomotopy.map i.hom ≫ adj.counit.app yH
  obtain ⟨ε, hε⟩ := (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map_surjective εH
  refine ⟨t, ε, fun x => ?_⟩
  let ev : ((_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) ⟶
      (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) t)) ≃
      (G.onHomotopy.obj ((_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x)) ⟶ yH) :=
    (Iso.homCongr (Iso.refl _) i).trans (adj.homEquiv _ _).symm
  have hev : (ev : _ → _) = (fun f => G.onHomotopy.map f ≫ (_root_.SerrePositivity.DifferentialGraded.toHomotopy R E).map ε) := by
    funext f
    change (adj.homEquiv _ _).symm ((𝟙 _) ≫ f ≫ i.hom) = _
    rw [Category.id_comp, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, hε]
  rw [← hev]
  exact ev.bijective
end SerrePositivity.InfinityCategories.Project.DerivedCategories
