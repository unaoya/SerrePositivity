module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.SupportModels
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # 完全対象上の幾何学的支持とスカラー支持

概要：完全モデルの幾何学的支持は恒等射の一様な冪消去と一致する。
方針：有界有限射影代表に移し、既存の零ホモトピーの構成を使う。
規約：一般の D_Z の対象についてはこの同値を主張しない。
使われ方：Perf_Z と既存の scalarSupported の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable {S : Type u} [CommRing S] {e : ℕ} (z : Fin e → S)

/-- 概要：有界有限射影複体の台は恒等射のスカラー冪による消去と同値である。
方針：幾何学的台から有限な項ごとの零ホモトピーを構成する既存定理を使う。
規約：Noether 性は不要。使われ方：完全モデルへの転送の基礎。 -/
lemma strictlyPerfect_support_iff_scalar (K : Complex S) (hK : strictlyPerfectComplex S K) :
    HasHomologySupportOn (supportZeroLocus (Ideal.span (Set.range z))) K ↔
      scalarSupported z ((HomotopyCategory.quotient _ _).obj K) := by
  have hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (K.X i) := by
    obtain ⟨a, b, ha, hb⟩ := hK.1
    let := ha
    let := hb
    exact ⟨a, b, fun i hi => hi.elim
      (fun h => K.isZero_of_isStrictlyGE a i h)
      (fun h => K.isZero_of_isStrictlyLE b i h)⟩
  have hproj : ∀ i, Projective (K.X i) := fun i => by
    have := (hK.2 i).2
    infer_instance
  constructor
  · intro h
    have hs := isSupported_of_homologySupport z K (fun i => (hK.2 i).1) hproj hbound h
    obtain ⟨v, hv, hh⟩ := hs.exists_pos
    exact ⟨v, hv, fun j => (nonempty_homotopy_smul_id_zero_iff _ _).1 (hh j)⟩
  · rintro ⟨v, _, hh⟩
    exact ((isSupported_iff z K).2 ⟨v, hh⟩).homologySupport

/-- 概要：完全モデルでは台条件と既存の scalarSupported が一致する。
方針：有限射影代表とのホモトピー圏の同型で両方の条件を移す。
規約：完全性の仮定を保持する。使われ方：Perf_Z の三つの判定条件の一つ。 -/
theorem perfectModel_support_iff_scalar (P : Complex S) (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel S P) :
    HasHomologySupportOn (supportZeroLocus (Ideal.span (Set.range z))) P ↔
      scalarSupported z ((HomotopyCategory.quotient _ _).obj P) := by
  obtain ⟨K, hK, ⟨h⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_iff S P).1 hP
  have hs : HasHomologySupportOn (supportZeroLocus (Ideal.span (Set.range z))) P ↔
      HasHomologySupportOn (supportZeroLocus (Ideal.span (Set.range z))) K :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty_quotient S _ P).symm.trans
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty S _).prop_iff_of_iso h).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportHomotopyProperty_quotient S _ K))
  exact hs.trans ((strictlyPerfect_support_iff_scalar z K hK).trans
    ((scalarSupported z).prop_iff_of_iso h).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
