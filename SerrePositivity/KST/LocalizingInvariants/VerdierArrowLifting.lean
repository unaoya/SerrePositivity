module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ArrowEssentialSurjectivity
public import SerrePositivity.KST.LocalizingInvariants.LocalizationEssentialSurjectivity
public import SerrePositivity.KST.LocalizingInvariants.LocalizationHomotopyCategory
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.WeakEquivalences
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberHoDenominators

/-!
概要：元の Verdier 商の実辺を分母で精密化し、同じ区間図式を持ち上げる。
方針：元の商の h 圏での右分数を実合成二単体に戻し、関手圏内の同型を構成する。
規約：辺の類の比較だけで全有限図式の局所化・core 逆像比較を結論しない。
使われ方：K-6 c5 の有限線型図式の持ち上げの一辺の段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)

include h

private lemma verdierHo_denominator_iff {x y : B.obj _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj B.obj) x y) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW (Truncated.HomotopyCategory.homMk e) ↔
      e.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) e
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.stableClosure_essentialImage h] at he
  exact he.symm

private lemma verdierHo_localization :
    (hoFunctor.map q.hom).toFunctor.IsLocalization
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW :=
  localizationHo_isLocalization q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.quotient
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW (verdierHo_denominator_iff h)

/-- 元の商の実辺は、元の実分母との合成を一つの指定二単体で回収する。 -/
lemma verdierProjection_edge_fraction {x y : B.obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj C.obj)
      (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) y)) :
    ∃ (a : B.obj _⦋0⦌)
      (s : Truncated.Edge (X := (truncation 2).obj B.obj) a x)
      (g : Truncated.Edge (X := (truncation 2).obj B.obj) a y),
      s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i ∧
      Nonempty (Truncated.Edge.CompStruct
        (s.map ((truncation 2).map q.hom)) f (g.map ((truncation 2).map q.hom))) := by
  let L := (hoFunctor.map q.hom).toFunctor
  let V := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)).trW
  have : L.IsLocalization V := verdierHo_localization h
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L V
    (X := HomotopyCategory.mk x) (Y := HomotopyCategory.mk y)
    (Truncated.HomotopyCategory.homMk f)
  have he := φ.map_s_comp_map L (Localization.inverts L V)
  rw [← hφ] at he
  rcases φ with @⟨a, s, hs, g⟩
  obtain ⟨a, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨s, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a x s
  obtain ⟨g, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a y g
  exact ⟨a, s, g, (verdierHo_denominator_iff h s).mp hs,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac he⟩

/-- 元の商内の指定辺を、実区間図式の同型を保って持ち上げる。
端点の変更は元の分母の像による可逆な比較で認証する。 -/
lemma verdierProjection_arrow_lift {x y : B.obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj C.obj)
      (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) y)) :
    ∃ g : (Δ[1] : SSet.{u}) ⟶ B.obj,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ q.hom) (SSet.yonedaEquiv.symm f.edge)) := by
  obtain ⟨a, s, g, hs, ⟨c⟩⟩ := verdierProjection_edge_fraction h f
  let sm := s.map ((truncation 2).map q.hom)
  let gm := g.map ((truncation 2).map q.hom)
  let j := Truncated.Edge.id (X := (truncation 2).obj C.obj)
    (q.hom.app (Opposite.op ⦋0⦌) y)
  have hsm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge sm := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible h s).mp hs
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge j := by
    change IsIso (Truncated.HomotopyCategory.homMk (Truncated.Edge.id _))
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have he : Truncated.HomotopyCategory.homMk gm ≫
      Truncated.HomotopyCategory.homMk j =
      Truncated.HomotopyCategory.homMk sm ≫ Truncated.HomotopyCategory.homMk f := by
    rw [show Truncated.HomotopyCategory.homMk j = 𝟙 _ from
      Truncated.HomotopyCategory.homMk_id _]
    exact (Category.comp_id (obj := hoFunctor.obj C.obj) _).trans
      (Truncated.HomotopyCategory.homMk_comp_homMk c).symm
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowFunctorIso_of_homMk_comm gm f sm j hsm hj he
  refine ⟨SSet.yonedaEquiv.symm g.edge, ⟨?_⟩⟩
  have hg : SSet.yonedaEquiv.symm gm.edge = SSet.yonedaEquiv.symm g.edge ≫ q.hom := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  rw [hg] at e
  exact e

/-- 元の商の後合成は、実区間を始域とする関手圏の頂点で本質的に全射。 -/
lemma verdierProjectionArrow_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective ((ihom (Δ[1] : SSet.{u})).map q.hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.arrowMap_isEssentiallySurjective q.hom
    (localization_isEssentiallySurjective q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.quotient)
    (fun f => verdierProjection_arrow_lift h f)

end SerrePositivity.KST.LocalizingInvariants
