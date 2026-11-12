module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuProjectionHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：元核包含の同じ全辺に恒等ホモトピーを置き、元二端点の全経路を保持する。
方針：元の辺上の定値ホモトピーと元恒等辺の単位評価を使う。
規約：元包含・元核・元中間圏を保持。使われ方：元下比較 prism の包含側境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma inclusionIdentityParameter {X : SSet.{u}} (x : X _⦋0⦌) :
    SSet.yonedaEquiv.symm (SSet.Edge.id x).edge = (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one x).symm

private lemma inclusionIdentityVertexPath (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 A)).edge := by
  have hi : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 A)).edge =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) := by
    change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (𝟙 A)).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id]
    exact inclusionIdentityParameter _
  simp only [SSet.yonedaEquiv_symm_zero, hi, SSet.comp_const]

private lemma inclusionConstantFunctorEdge {A X : SSet.{u}} (f : A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm f)) =
      SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  apply SSet.Truncated.Edge.ext
  have hc : curry (fst A (Δ[1] : SSet.{u}) ≫ f) =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj X) :=
    (congrArg (fun k => curry k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex (L := (Δ[1] : SSet.{u})) f)).symm.trans
      (curry_uncurry _)
  exact (congrArg SSet.yonedaEquiv hc).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))

private lemma inclusionConstantEndpoints (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (SSet.RelativeMorphism.Homotopy.refl
          (SSet.RelativeMorphism.botEquiv.symm (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow f).edge))).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 A)).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (SSet.RelativeMorphism.Homotopy.refl
          (SSet.RelativeMorphism.botEquiv.symm (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow f).edge))).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 B)).edge := by
  have hs : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow f).edge =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) := by
    rw [← Category.assoc, whiskerRight_fst, Category.assoc,
      SSet.Edge.δ_one_yonedaEquiv_symm]
  have ht : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow f).edge =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex B) := by
    rw [← Category.assoc, whiskerRight_fst, Category.assoc,
      SSet.Edge.δ_zero_yonedaEquiv_symm]
  exact ⟨hs.trans (inclusionIdentityVertexPath A), ht.trans (inclusionIdentityVertexPath B)⟩

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "A" => dgKInputStableValue R (dgOdotMilnorCellInput R d)
local notation "i" => dgOdotMilnorFlatKernelExactMap R d

/-- 概要：元核包含の同じ全一単体の恒等ホモトピー。
方針：元辺に同じ定値ホモトピーを置く。
規約：新たな辺を選ばない。使われ方：元下比較 prism の包含側境界。 -/
def dgOdotMilnorNuInclusionArrowHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (i)).edge)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (i)).edge) :=
  SSet.RelativeMorphism.Homotopy.refl
    (SSet.RelativeMorphism.botEquiv.symm (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (i)).edge))

/-- 概要：元包含の恒等ホモトピーは元全辺の同じ第一射影による定値族。
方針：同じ恒等ホモトピーの定義。
規約：元の全パラメータを保持。使われ方：恒等経路の厳密回収。 -/
lemma dgOdotMilnorNuInclusionArrowHomotopy_h :
    (dgOdotMilnorNuInclusionArrowHomotopy R d).h =
      fst (Δ[1] : SSet.{u + 2}) Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (i)).edge := rfl

/-- 概要：元包含の恒等ホモトピーの関手辺は元関手頂点の恒等辺。
方針：同じ定値族の curry と元恒等辺を照合する。
規約：元実辺の等号。使われ方：指定包含境界の同一性。 -/
lemma dgOdotMilnorNuInclusionArrowHomotopy_functorEdge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuInclusionArrowHomotopy R d) =
      SSet.Truncated.Edge.id (X := (truncation 2).obj
        ((ihom (Δ[1] : SSet.{u + 2})).obj _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (i)).edge)) :=
  inclusionConstantFunctorEdge _

/-- 概要：元包含の同じ実ホモトピーが与える比較の射は恒等。
方針：元恒等関手辺の回収をホモトピー圏へ写す。
規約：元関手の恒等射そのもの。使われ方：Sp の指定包含比較の保持。 -/
lemma dgOdotMilnorNuInclusionArrowHomotopy_comparison :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuInclusionArrowHomotopy R d)) =
      𝟙 (SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (i)).edge))) :=
  (congrArg SSet.Truncated.HomotopyCategory.homMk
    (dgOdotMilnorNuInclusionArrowHomotopy_functorEdge R d)).trans
      (SSet.Truncated.HomotopyCategory.homMk_id _)

/-- 概要：元包含の恒等ホモトピーは元核・元中間圏の恒等経路を両端に持つ。
方針：同じ元完全射の両端点の単位評価を使う。
規約：全一単体の厳密等号。使われ方：元三境界の厳密貼り合わせ。 -/
lemma dgOdotMilnorNuInclusionArrowHomotopy_paths :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuInclusionArrowHomotopy R d).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuInclusionArrowHomotopy R d).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).edge :=
  inclusionConstantEndpoints (K) (A) (i)

end SerrePositivity.KST.SConstruction
