module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExPairingBijection
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore

/-!
# X→Ex(X) の proper pairing

概要：次元別の型 II とその拡張を Mathlib の PairingCore にまとめる。
方針：全次元の添字を Sigma 型で表し、前段の像に入るかどうかで全単射を与える。
規約：Moss 2020 Theorem 22、Lemmas 27・28・29。正則性はこの構成に含めない。
使われ方：単位の anodyne 性に向けた regular pairing の構成。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open scoped _root_.Simplicial

/--
概要：単位の像の外の非退化単体を、型 II とその対応先に分割する pairing の核。
方針：型 II の全次元の直和を添字とし、最小複雑度の拡張を型 I とする。
規約：Moss 2020 Theorem 22 の pairing。Mathlib PairingCore の規約を使う。
使われ方：proper pairing と先行関係の構成。
-/
def exPairingCore (X : SSet.{u}) : (SSet.Subcomplex.range (exUnitAt X)).PairingCore where
  ι := Σ n : ℕ, exTypeTwo X n
  dim s := s.1
  simplex s := exPairingStep X s.1 s.2.val
  index s := (exComplexityLevel X _ s.2.val).succ
  nonDegenerate₁ s := exPairingStep_nonDegenerate_target X s.1 s.2.val s.2.property
  nonDegenerate₂ s := by
    simpa only [exPairingStep, exExpansion_face] using s.2.property.1
  notMem₁ s := by
    change exPairingStep X s.1 s.2.val ∉ Set.range ((exUnitAt X).app _)
    exact (exPairingStep_mem_typeOne X s.1 s.2.val s.2.property).2.1
  notMem₂ s := by
    simp only [exPairingStep, exExpansion_face]
    exact s.2.property.2.1
  injective_type₁' {s t} h := by
    obtain ⟨n, s⟩ := s
    obtain ⟨m, t⟩ := t
    have hd : n = m := Nat.succ.inj (SSet.S.dim_eq_of_mk_eq h)
    subst m
    have he := (exPairingStep_injective X n) ((SSet.S.ext_iff _ _).mp h)
    exact congrArg (Sigma.mk n) (Subtype.ext he)
  injective_type₂' {s t} h := by
    simp only [exPairingStep, exExpansion_face] at h
    obtain ⟨n, s⟩ := s
    obtain ⟨m, t⟩ := t
    have hd : n = m := SSet.S.dim_eq_of_mk_eq h
    subst m
    exact congrArg (Sigma.mk n) (Subtype.ext ((SSet.S.ext_iff _ _).mp h))
  type₁_ne_type₂' s t h := by
    simp only [exPairingStep, exExpansion_face] at h
    obtain ⟨n, s⟩ := s
    obtain ⟨m, t⟩ := t
    have hd : n + 1 = m := SSet.S.dim_eq_of_mk_eq h
    subst m
    apply t.property.2.2
    exact ⟨s.val, (SSet.S.ext_iff _ _).mp h⟩
  surjective' x := by
    obtain ⟨n, s, hnd, hu, rfl⟩ := x.mk_surjective
    change s ∉ Set.range ((exUnitAt X).app _) at hu
    by_cases hi : s ∈ exPairingImage X n
    · cases n with
      | zero => exact (Set.notMem_empty s hi).elim
      | succ n =>
          obtain ⟨t, ht⟩ := hi
          have hI : exPairingStep X n t ∈ exTypeOne X (n + 1) := by
            rw [ht]
            exact ⟨hnd, hu, ⟨t, ht⟩⟩
          refine ⟨⟨n, ⟨t, exPairingStep_mem_typeTwo_of_typeOne X n t hI⟩⟩, Or.inl ?_⟩
          exact congrArg SSet.S.mk ht.symm
    · refine ⟨⟨n, ⟨s, hnd, hu, hi⟩⟩, Or.inr ?_⟩
      simp only [exPairingStep, exExpansion_face]
      rfl

/--
概要：構成した pairing の核は proper である。
方針：型 II の指定面の一意性を PairingCore のフィールドに移す。
規約：Moss 2020 Lemma 29。
使われ方：全次元の pairing の properness インスタンス。
-/
instance exPairingCore_isProper (X : SSet.{u}) : (exPairingCore X).IsProper where
  isUniquelyCodimOneFace s := by
    change SSet.S.IsUniquelyCodimOneFace
      (SSet.S.mk ((SSet.ex.obj X).δ (exComplexityLevel X _ s.2.val).succ
        (exPairingStep X s.1 s.2.val))) (SSet.S.mk (exPairingStep X s.1 s.2.val))
    simpa only [exPairingStep, exExpansion_face] using
      exPairingStep_isUniquelyCodimOneFace X s.1 s.2.val s.2.property

/--
概要：単位の像に対する全次元の pairing。
方針：明示的な proper pairing の核から Mathlib の pairing を得る。
規約：Moss 2020 Theorem 22。正則性と anodyne 性は別途証明する。
使われ方：先行関係の整礎性を検証する対象。
-/
def exPairing (X : SSet.{u}) : (SSet.Subcomplex.range (exUnitAt X)).Pairing :=
  (exPairingCore X).pairing

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
