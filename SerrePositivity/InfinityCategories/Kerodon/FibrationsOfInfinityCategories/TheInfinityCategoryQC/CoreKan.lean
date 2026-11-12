module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreFaces
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory の core は Kan 複体。
方針：周囲でホーンを充填し、三角形の二対三性または高次ホーンの全辺から core に戻す。
規約：一次ホーンは定値辺で扱い、全ての外側ホーンも充填する。
使われ方：Kerodon Corollary 4.4.3.11（Tag 01H1）、Proposition 5.5.3.3（Tag 020B） の局所 Kan 性。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：core 内の二次以上のホーンの充填は周囲のどの充填でも core に属する。
方針：二次では新しい辺の可逆性、高次では全辺が既にホーンに属することを使う。
規約：周囲の quasicategory 性は充填の選択にのみ必要なので本補題には仮定しない。
使われ方：Kerodon Corollary 4.4.3.11（Tag 01H1）、周囲のホーン充填から core への帰還。 -/
lemma quasicategoryCore_horn_filler_mem {X : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (a : (horn (n + 2) i : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}))
    (F : (Δ[n + 2] : SSet.{u}) ⟶ X)
    (hF : (horn (n + 2) i).ι ≫ F = a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι) :
    SSet.yonedaEquiv F ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).obj (Opposite.op ⦋n + 2⦌) := by
  cases n with
  | zero =>
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_triangle_iff _).2
    have hfaces (j : Fin 3) (hj : j ≠ i) :
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X.δ j (SSet.yonedaEquiv F))) := by
      rw [← stdSimplex.yonedaEquiv_δ_comp]
      have hh : stdSimplex.δ j ≫ F =
          (horn.ι i j hj ≫ a) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι := by
        rw [← horn.ι_ι_assoc i j hj, hF, Category.assoc]
      rw [hh]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge (SSet.yonedaEquiv (horn.ι i j hj ≫ a))
    intro j
    by_cases hj : j = i
    · subst j
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_triangle_missing (SSet.yonedaEquiv F) i hfaces
    · exact hfaces j hj
  | succ n =>
    intro f
    let e : (horn (n + 3) i : SSet.{u}) _⦋1⦌ :=
      ⟨stdSimplex.objEquiv.symm f, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edge_mem_horn_of_three_le n i _⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((SSet.yonedaEquiv.symm (SSet.yonedaEquiv F)).app (Opposite.op ⦋1⦌)
        (stdSimplex.objEquiv.symm f)))
    rw [Equiv.symm_apply_apply]
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hF (Opposite.op ⦋1⦌)) e
    change F.app (Opposite.op ⦋1⦌) e.val = (a.app (Opposite.op ⦋1⦌) e).val at h
    rw [h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge (a.app (Opposite.op ⦋1⦌) e)

/-- 概要：quasicategory の core は全てのホーンを充填する Kan 複体。
方針：内ホーンは quasicategory 性、外ホーンは指定辺の可逆性で周囲に充填する。
規約：モデル構造は使わず、一次ホーンも含む KanComplex の定義を満たす。
使われ方：Kerodon Corollary 4.4.3.11（Tag 01H1）、Proposition 5.5.3.3（Tag 020B） の関手単体集合の core。 -/
@[kerodon 01H1, kerodon 020B]
instance quasicategoryCore_kanComplex (X : SSet.{u}) [Quasicategory X] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) := by
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
    obtain ⟨a, ha⟩ := hf.exists_desc
    let a' := a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι
    have hfill : ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ X, (horn (n + 2) i).ι ≫ F = a' := by
      by_cases hi0 : i = 0
      · subst i
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasInitialHornFillers_of_isInvertibleEdge
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (a'.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n))) n a' rfl
      · by_cases hilast : i = Fin.last (n + 2)
        · subst i
          exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (a'.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n)))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n))) n a' rfl
        · have hi₀ : (0 : Fin (n + 3)) < i := by
            change 0 < i.val
            have h : i.val ≠ 0 := fun hh ↦ hi0 (Fin.ext hh)
            omega
          have hi₁ : i < Fin.last (n + 2) := by
            change i.val < n + 2
            have h : i.val ≠ n + 2 := fun hh ↦ hilast (Fin.ext hh)
            have := i.isLt
            omega
          obtain ⟨F, hF⟩ := Quasicategory.hornFilling hi₀ hi₁ a'
          exact ⟨F, hF.symm⟩
    obtain ⟨F, hF⟩ := hfill
    let F' : (Δ[n + 2] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) :=
      SSet.yonedaEquiv.symm ⟨SSet.yonedaEquiv F, quasicategoryCore_horn_filler_mem n i a F hF⟩
    have hF' : F' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι = F := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp]
      change (SSet.yonedaEquiv F').val = SSet.yonedaEquiv F
      rw [Equiv.apply_symm_apply]
    have hboundary : (horn (n + 2) i).ι ≫ F' = a := by
      apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι).1
      rw [Category.assoc, hF']
      exact hF
    refine ⟨F', ?_⟩
    intro j hj
    rw [← horn.ι_ι_assoc i j hj, hboundary]
    exact ha j hj

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
