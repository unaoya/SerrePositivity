module
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanFiniteFactorization
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakContractibility
public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyClasses
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension

/-! # 有限図式の零ホモトピー span による弱可縮性

概要：全有限図式が定値図式へホモトピーの span で結ばれれば、対象は弱可縮である。
方針：有限部分での収縮を連続 Kan 置換へ送り、全境界の充填を有限因子化で構成する。
規約：元の対象の Kan 性を仮定しない。使われ方：Quillen A の slice 引き戻しの検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet F2
open scoped Simplicial

/-- 全有限図式が定値図式へ零ホモトピーの span を持てば、対象は弱可縮。 -/
lemma isWeaklyContractible_of_finiteNullSpans (X : SSet.{u})
    (h : ∀ {K : SSet.{u}} [K.Finite] (f : K ⟶ X),
      ∃ u : K ⟶ X, ∃ x : X _⦋0⦌,
        Nonempty (SSet.Homotopy u f) ∧ Nonempty (SSet.Homotopy u (SSet.const x))) :
    IsWeaklyContractible X := by
  have hm {K : SSet.{u}} [K.Finite] (f : K ⟶ X) :
      ∃ x : (continuousKanReplacement.obj X) _⦋0⦌,
        SSet.π₀.mk (functorVertex (continuousKanReplacement.map f)) =
          SSet.π₀.mk (functorVertex (SSet.const x)) := by
    obtain ⟨u, x, ⟨H₀⟩, ⟨H₁⟩⟩ := h f
    let x' := (continuousKanReplacementUnit.app X).app (Opposite.op ⦋0⦌) x
    refine ⟨x', ?_⟩
    apply (continuousKanReplacementUnit_isWeakHomotopyEquivalence K
      (continuousKanReplacement.obj X)).injective
    change SSet.π₀.mk (functorVertex
        (continuousKanReplacementUnit.app K ≫ continuousKanReplacement.map f)) =
      SSet.π₀.mk (functorVertex (continuousKanReplacementUnit.app K ≫ SSet.const x'))
    rw [← continuousKanReplacementUnit.naturality f, SSet.comp_const]
    change SSet.π₀.mk (functorVertex (f ≫ continuousKanReplacementUnit.app X)) =
      SSet.π₀.mk (functorVertex (SSet.const x'))
    have h₀ := (functorVertex_piZero_eq_iff_homotopy _ _).2
      ⟨functorHomotopyPostcomp H₀ (continuousKanReplacementUnit.app X)⟩
    have h₁ := (functorVertex_piZero_eq_iff_homotopy _ _).2
      ⟨functorHomotopyPostcomp H₁ (continuousKanReplacementUnit.app X)⟩
    simpa only [x', SSet.const_comp] using! h₀.symm.trans h₁
  have hc : IsContractibleKan (continuousKanReplacement.obj X) := by
    intro n b
    obtain ⟨A, g, hg⟩ := continuousKanReplacement_boundary_factorization X n b
    obtain ⟨x, hx⟩ := hm A.val.ι
    have hh := congrArg (SSet.mapπ₀ ((pre g).app (continuousKanReplacement.obj X))) hx
    change SSet.π₀.mk (functorVertex (g ≫ continuousKanReplacement.map A.val.ι)) =
      SSet.π₀.mk (functorVertex (g ≫ SSet.const x)) at hh
    rw [hg, SSet.comp_const] at hh
    obtain ⟨e⟩ := nonempty_vertexIso_of_piZero_eq hh.symm
    exact (show FunctorIso (SSet.const x) b from e).exists_boundaryFilling
      ⟨SSet.const x, by rw [SSet.comp_const]⟩
  exact (continuousKanReplacementUnit_isWeakHomotopyEquivalence X).weaklyContractible_iff.2
    hc.isWeaklyContractible

end SerrePositivity.InfinityCategories
