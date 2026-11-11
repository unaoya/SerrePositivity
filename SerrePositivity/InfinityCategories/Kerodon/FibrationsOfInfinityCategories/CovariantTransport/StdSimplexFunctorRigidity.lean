module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-!
概要：標準単体への同型な二つの関手は厳密に一致する。
方針：両方向のホモトピーから各頂点の値の順序関係を得て、反対称性を使う。
規約：始域には quasicategory 性を要求しない。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、延長した比較の区間への射影の厳密化。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：標準単体へのホモトピーは各頂点で値の順序関係を与える。
方針：係数頂点を固定した区間の像を取り、その両端と単調性を使う。
規約：ホモトピーの向きは f から g。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、区間への射影の同型から等式を得る補題。 -/
lemma stdSimplex_homotopy_vertex_le {A : SSet.{u}} {n : ℕ}
    {f g : A ⟶ (Δ[n] : SSet.{u})} (H : SSet.Homotopy f g) (x : A _⦋0⦌) :
    (f.app (Opposite.op ⦋0⦌) x) 0 ≤ (g.app (Opposite.op ⦋0⦌) x) 0 := by
  let q : (Δ[1] : SSet.{u}) ⟶ Δ[n] := lift (SSet.const x) (𝟙 Δ[1]) ≫ H.h
  have h0 : stdSimplex.δ (1 : Fin 2) ≫ q = SSet.yonedaEquiv.symm (f.app _ x) := by
    change (stdSimplex.δ (1 : Fin 2) ≫ lift (SSet.const x) (𝟙 Δ[1])) ≫ H.h = _
    have he : stdSimplex.δ (1 : Fin 2) ≫ lift (SSet.const x) (𝟙 Δ[1]) =
        SSet.yonedaEquiv.symm x ≫ SSet.ι₀ := by
      rw [stdSimplex.δ_one_eq_const, SSet.yonedaEquiv_symm_zero]
      rfl
    rw [he, Category.assoc, H.h₀, SSet.yonedaEquiv_symm_comp]
  have h1 : stdSimplex.δ (0 : Fin 2) ≫ q = SSet.yonedaEquiv.symm (g.app _ x) := by
    change (stdSimplex.δ (0 : Fin 2) ≫ lift (SSet.const x) (𝟙 Δ[1])) ≫ H.h = _
    have he : stdSimplex.δ (0 : Fin 2) ≫ lift (SSet.const x) (𝟙 Δ[1]) =
        SSet.yonedaEquiv.symm x ≫ SSet.ι₁ := by
      rw [stdSimplex.δ_zero_eq_const, SSet.yonedaEquiv_symm_zero]
      rfl
    rw [he, Category.assoc, H.h₁, SSet.yonedaEquiv_symm_comp]
  let σ := SSet.yonedaEquiv q
  have hσ : SSet.yonedaEquiv.symm σ = q := SSet.yonedaEquiv.symm_apply_apply q
  rw [← hσ, stdSimplex.δ_comp_yonedaEquiv_symm] at h0 h1
  have hz := congrArg (fun s : (Δ[n] : SSet.{u}) _⦋0⦌ ↦ s 0)
    (SSet.yonedaEquiv.symm.injective h0)
  have ho := congrArg (fun s : (Δ[n] : SSet.{u}) _⦋0⦌ ↦ s 0)
    (SSet.yonedaEquiv.symm.injective h1)
  change σ 0 = (f.app _ x) 0 at hz
  change σ 1 = (g.app _ x) 0 at ho
  rw [← hz, ← ho]
  exact (stdSimplex.objEquiv σ).toOrderHom.monotone (by decide)

/-- 概要：標準単体への同型な二つの関手は射として一致する。
方針：同型とその逆から両方向の頂点の不等式を得て反対称性を使う。
規約：関手の同型は関手単体集合のホモトピー圏の同型。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、区間上の射の厳密な一致。 -/
lemma stdSimplex_eq_of_functorIso {A : SSet.{u}} {n : ℕ}
    {f g : A ⟶ (Δ[n] : SSet.{u})} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  apply stdSimplex.ext
  intro i
  have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
  subst i
  exact le_antisymm (stdSimplex_homotopy_vertex_le e.simplicialHomotopy x)
    (stdSimplex_homotopy_vertex_le (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy e.symm) x)

/-- 概要：前合成の同値を持つ射上で一致する標準単体への二射は等しい。
方針：前合成の充満忠実性で同型を戻し、標準単体への関手の同型を等式へ移す。
規約：比較する射の始域の充填性や前合成する射の単射性は要求しない。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、円柱上の底の条件から全体の底の条件を得る。 -/
lemma IsPrecompositionEquivalence.stdSimplex_hom_ext {A B : SSet.{u}} {i : A ⟶ B}
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) {n : ℕ} {f g : B ⟶ (Δ[n] : SSet.{u})}
    (h : i ≫ f = i ≫ g) : f = g := by
  apply stdSimplex_eq_of_functorIso
  apply (hi Δ[n]).isFullyFaithful.preimageVertexIso
  exact eqToIso (congrArg (fun q : A ⟶ (Δ[n] : SSet.{u}) ↦
    SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) h)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsPrecompositionEquivalence (stdSimplex_hom_ext)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
