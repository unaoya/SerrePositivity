module

public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# semiperfectoid 環

BS 著者版 §7.1 の、p 完備な perfectoid 環の商という条件を名前にする。
基底代数の構造はこの性質に不要。全射性と完備性を別の条件として保持する。
-/

@[expose] public section
universe u
namespace SerrePositivity.BhattScholze

/-- BS 著者版 §7.1 の semiperfectoid 環。
p 完備な環 S が、ある整 perfectoid 環の全射像であること。
完備性は既存の導来 p 完備性で表し、被覆は同じ宇宙で選ぶ。 -/
def Semiperfectoid.IsSemiperfectoid (p : ℕ) [Fact p.Prime] (S : Type u) [CommRing S] : Prop :=
  _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S) ∧
    ∃ (T : CommRingCat.{u}) (q : T →+* S), _root_.SerrePositivity.IsIntegralPerfectoid T p ∧ Function.Surjective q

/-- semiperfectoid の定義から導来 p 完備性を取り出す。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsSemiperfectoid.isModuleComplete {p : ℕ} [Fact p.Prime]
    {S : Type u} [CommRing S] (h : _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsSemiperfectoid p S) :
    _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S) := h.1

/-- semiperfectoid の定義から perfectoid の全射被覆を取り出す。
完備性だけから被覆の存在を推論しない。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsSemiperfectoid.exists_surjective {p : ℕ} [Fact p.Prime]
    {S : Type u} [CommRing S] (h : _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsSemiperfectoid p S) :
    ∃ (T : CommRingCat.{u}) (q : T →+* S), _root_.SerrePositivity.IsIntegralPerfectoid T p ∧ Function.Surjective q := h.2

/-- 指定された perfectoid の全射像が p 完備なら semiperfectoid。
新たな完備性の定理を使わず、定義の二条件を組み合わせる。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsSemiperfectoid.of_surjective {p : ℕ} [Fact p.Prime]
    {T S : Type u} [CommRing T] [CommRing S] (q : T →+* S)
    (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p) (hq : Function.Surjective q)
    (hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.IsSemiperfectoid p S := ⟨hS, CommRingCat.of T, q, hT, hq⟩

end SerrePositivity.BhattScholze
