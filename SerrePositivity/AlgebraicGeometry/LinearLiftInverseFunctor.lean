module

public import SerrePositivity.AlgebraicGeometry.LinearSequenceDirectLimit
public import Mathlib.Algebra.Module.Projective

/-!
概要：KST §5、Stacks 05DP・059X の加群列から全射への持ち上げの実際の逆系。
方針：持ち上げの集合を等式で切り出し、全遷移での前合成を関手の射にする。
規約：射影性の存在を関手のデータに含めず、各段階の非空性は後から証明する。
使われ方：双対像安定化と核値補正から整合的な持ち上げを得る。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

/--
概要：指定された二つの線形写像の間の実際の持ち上げの集合。
方針：線形写像とその後合成の等式の部分型を取る。
規約：KST §5、Stacks 05DP・059X、持ち上げの存在は定義に含めない。
使われ方：加群列の各段階の持ち上げの対象。
-/
def LinearLift {R U E M : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup E] [Module R E] [AddCommGroup M] [Module R M]
    (π : E →ₗ[R] M) (q : U →ₗ[R] M) := {l : U →ₗ[R] E // π.comp l = q}

variable (R : Type u) [CommRing R] (F : ℕ → Type u)
  [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
  (a : ∀ n, F n →ₗ[R] F (n + 1))
  {M E : Type u} [AddCommGroup M] [Module R M] [AddCommGroup E] [Module R E]
  (q : ∀ n, F n →ₗ[R] M) (hq : ∀ n, (q (n + 1)).comp (a n) = q n) (π : E →ₗ[R] M)

/--
概要：後続段階の持ち上げは遷移写像との前合成で初段の持ち上げを与える。
方針：評価の全遷移に対する可換式を使う。
規約：KST §5、Stacks 05DP・059X、任意の n≤m の実際の写像。
使われ方：持ち上げの逆系の射。
-/
def linearSequenceLiftRestrict (n m : ℕ) (h : n ≤ m) (l : LinearLift π (q m)) :
    LinearLift π (q n) :=
  ⟨l.val.comp (linearSequenceMap R F a n m h), by
    ext x
    change π (l.val (linearSequenceMap R F a n m h x)) = q n x
    have hl := congrArg (fun f : F m →ₗ[R] M => f (linearSequenceMap R F a n m h x)) l.property
    exact hl.trans (linearSequenceMap_eval R F a q hq n m h x)⟩

/--
概要：加群列から指定射への持ち上げの集合は自然数逆系を成す。
方針：全遷移での前合成を射とし、有向系の恒等・合成の法則から関手の法則を得る。
規約：KST §5、Stacks 05DP・059X、各持ち上げの存在は仮定しない。
使われ方：持ち上げの集合の Mittag–Leffler 性と section の存在。
-/
def linearSequenceLiftFunctor : ℕᵒᵖ ⥤ Type u where
  obj i := LinearLift π (q i.unop)
  map {i j} f := ↾(linearSequenceLiftRestrict R F a q hq π j.unop i.unop (leOfHom f.unop))
  map_id i := by
    ext l
    apply Subtype.ext
    ext x
    exact congrArg l.val (DirectedSystem.map_self' (linearSequenceMap R F a) x)
  map_comp {i j k} f g := by
    ext l
    apply Subtype.ext
    ext x
    exact (congrArg l.val (DirectedSystem.map_map' (linearSequenceMap R F a)
      (leOfHom g.unop) (leOfHom f.unop) x)).symm

/--
概要：射影加群から全射への持ち上げの集合は非空。
方針：射影加群の実際の持ち上げ写像を選ぶ。
規約：KST §5、Stacks 05DP・059X、加群の有限性は不要。
使われ方：有限自由列の各段階の持ち上げの非空性。
-/
theorem nonempty_linearLift_of_projective
    {R U E M : Type*} [CommRing R] [AddCommGroup U] [Module R U] [Module.Projective R U]
    [AddCommGroup E] [Module R E] [AddCommGroup M] [Module R M]
    (π : E →ₗ[R] M) (q : U →ₗ[R] M) (hπ : Function.Surjective π) :
    Nonempty (LinearLift π q) := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property π q hπ
  exact ⟨⟨l, hl⟩⟩

/--
概要：自由加群列から全射への持ち上げ逆系は各段階で非空。
方針：各基底から射影性を得て全射の持ち上げ性を適用する。
規約：KST §5、Stacks 05DP・059X、基底の有限性は非空性には不要。
使われ方：Mittag–Leffler 逆系の section の存在へ渡す。
-/
theorem linearSequenceLiftFunctor_nonempty_of_basis
    {σ : ℕ → Type v} (b : ∀ n, Module.Basis (σ n) R (F n))
    (hπ : Function.Surjective π) (i : ℕᵒᵖ) :
    Nonempty ((linearSequenceLiftFunctor R F a q hq π).obj i) := by
  let : Module.Projective R (F i.unop) := Module.Projective.of_basis (b i.unop)
  exact nonempty_linearLift_of_projective π (q i.unop) hπ

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
