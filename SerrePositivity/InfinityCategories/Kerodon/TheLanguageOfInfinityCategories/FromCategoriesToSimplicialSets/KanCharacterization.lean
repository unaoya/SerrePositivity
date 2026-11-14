module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornDuality
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory が Kan 複体であることとホモトピー圏が亜群であることの同値。
方針：内ホーンは quasicategory 性、外ホーンは指定する辺の可逆性から充填する。
規約：一次ホーンは定数辺で別途充填する。
使われ方：HTT Proposition 1.2.5.1、Kerodon Proposition 4.4.2.1（Tag 019D）。

対応節は Kerodon 1.3（Tag 002L）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets

/-- 概要：ホモトピー圏が亜群である quasicategory は Kan 複体。
方針：二次以上の左右の外側ホーンは Joyal の定理で、内側は quasicategory 性で充填する。
規約：全ての次数と全てのホーンを扱う。
使われ方：HTT Proposition 1.2.5.1、Kerodon Proposition 4.4.2.1（Tag 019D） の逆向き。 -/
lemma kanComplex_of_isGroupoid (X : SSet.{u}) [Quasicategory X]
    [IsGroupoid (hoFunctor.obj X)] : KanComplex X := by
  rw [KanComplex.iff]
  intro n i f hf
  cases n with
  | zero =>
    have hi : i.rev ≠ i := by fin_cases i <;> decide
    refine ⟨SSet.const (SSet.yonedaEquiv (f i.rev hi)), ?_⟩
    intro j hj
    have hj' : j = i.rev := by
      fin_cases i <;> fin_cases j <;> first | rfl | exact (hj rfl).elim
    subst j
    rw [SSet.comp_const]
    exact (SSet.yonedaEquiv_symm_zero _).symm.trans (SSet.yonedaEquiv.symm_apply_apply _)
  | succ n =>
    obtain ⟨σ, hσ⟩ := hf.exists_desc
    have hfill : ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ X, (horn (n + 2) i).ι ≫ F = σ := by
      by_cases hi0 : i = 0
      · subst i
        let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n))
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasInitialHornFillers_of_isInvertibleEdge e
          (IsGroupoid.all_isIso (C := hoFunctor.obj X)
            (SSet.Truncated.HomotopyCategory.homMk e)) n σ rfl
      · by_cases hilast : i = Fin.last (n + 2)
        · subst i
          let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n))
          exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge e
            (IsGroupoid.all_isIso (C := hoFunctor.obj X)
              (SSet.Truncated.HomotopyCategory.homMk e)) n σ rfl
        · have hi₀ : (0 : Fin (n + 3)) < i := by
            change 0 < i.val
            have h : i.val ≠ 0 := fun hh ↦ hi0 (Fin.ext hh)
            omega
          have hi₁ : i < Fin.last (n + 2) := by
            change i.val < n + 2
            have h : i.val ≠ n + 2 := fun hh ↦ hilast (Fin.ext hh)
            have := i.isLt
            omega
          obtain ⟨F, hF⟩ := Quasicategory.hornFilling hi₀ hi₁ σ
          exact ⟨F, hF.symm⟩
    obtain ⟨F, hF⟩ := hfill
    refine ⟨F, ?_⟩
    intro j hj
    rw [← horn.ι_ι_assoc i j hj, hF]
    exact hσ j hj

/-- 概要：quasicategory が Kan 複体であることとホモトピー圏が亜群であることは同値。
方針：Kan 複体の可逆性と外側ホーンの可逆辺による充填を組み合わせる。
規約：亜群性は通常の命題値クラス IsGroupoid。
使われ方：HTT Proposition 1.2.5.1、Kerodon Proposition 4.4.2.1（Tag 019D）。 -/
@[kerodon 0037, kerodon 0052]
lemma kanComplex_iff_isGroupoid (X : SSet.{u}) [Quasicategory X] :
    KanComplex X ↔ IsGroupoid (hoFunctor.obj X) := by
  constructor
  · intro h
    have := h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid X
  · intro h
    have := h
    exact kanComplex_of_isGroupoid X

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "3.3.1.5" (partial := component) "仮定：準圏のホモトピー圏が亜群（Lean は Ext の全辺が同値であることを既知とする）。結論：その準圏が Kan 複体となる（Ext が亜群と分かった後の結論に一致）。色の準圏の Kan 性から Ext の全辺の同値性を導く部分は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_of_isGroupoid
attribute [cite HTT "1.2.5.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_iff_isGroupoid
attribute [cite HTT "2.1.3.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_iff_isGroupoid
