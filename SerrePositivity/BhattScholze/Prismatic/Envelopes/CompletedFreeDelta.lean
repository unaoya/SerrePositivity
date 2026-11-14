module

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.Envelope

/-!
# 完備自由 δ 環の普遍性

## 概要
完備自由 δ 環からの射を、基底射と初期座標の像で記述する。

## 方針
自由 δ 環の評価と、導来 (p,d) 完備な標的への一意延長を合成する。

## 規約
完備化は零次ホモロジーで取り、標的の完備性は基底生成元の像について仮定する。

## 使われ方
変数に沿う envelope と affine Čech–Alexander 模型の座標写像。
-/

@[expose] public section
noncomputable section

universe u

open CategoryTheory
open SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (S : Type u)

local notation "B" => RelativeFreeDeltaRing (R := A) S
local notation "dB" => algebraMap A B P.generator
local notation "j" => pdCompletionUnit B p dB

/-- 完備自由 δ 環の初期座標。 -/
def completedFreeDeltaVariable (s : S) : completedFreeDelta P S :=
  j (MvPolynomial.X (s, 0))

/-- 概要：完備自由 δ 環からの δ 射は、基底射と初期座標の像で一意に決まる。
方針：自由 δ 環で評価し、標的の完備性から一意に延長する。
規約：標的は p と基底の生成元の像について導来完備。
使われ方：変数に沿う envelope と Čech の各座標写像。 -/
theorem existsUnique_completedFreeDeltaHom {D : Type u} [CommRing D]
    (E : DeltaStructure p D) (f : A →+* D) (hf : P.deltaStructure.IsDeltaHom E f)
    (hp : IsModuleComplete D (p : D) (ModuleCat.of D D))
    (hd : IsModuleComplete D (f P.generator) (ModuleCat.of D D)) (a : S → D) :
    ∃! g : completedFreeDelta P S →+* D,
      (completedFreeDeltaStructure P S).IsDeltaHom E g ∧
        g.comp (completedFreeDeltaBase P S) = f ∧
        ∀ s, g (completedFreeDeltaVariable P S s) = a s := by
  let raw : B →+* D := relativeFreeDeltaEval E f a
  have rawδ : (relativeFreeDeltaStructure S P.deltaStructure).IsDeltaHom E raw :=
    relativeFreeDeltaEval_isDeltaHom P.deltaStructure E f hf a
  have rawBase : raw.comp (algebraMap A B) = f := by
    ext x
    exact relativeFreeDeltaEval_C E f a x
  have hraw : IsModuleComplete D (raw dB) (ModuleCat.of D D) := by
    rw [show raw dB = f P.generator from RingHom.congr_fun rawBase P.generator]
    exact hd
  obtain ⟨g, hg, huniq⟩ := existsUnique_deltaPDCompletionHom
    (relativeFreeDeltaStructure S P.deltaStructure) dB E raw rawδ hp hraw
  refine ⟨g, ⟨hg.1, ?_, ?_⟩, ?_⟩
  · change g.comp ((j).comp (algebraMap A B)) = f
    rw [← RingHom.comp_assoc, hg.2, rawBase]
  · intro s
    change (g.comp j) (MvPolynomial.X (s, 0)) = a s
    rw [hg.2]
    exact relativeFreeDeltaEval_X E f a s 0
  · intro h hh
    apply huniq
    refine ⟨hh.1, ?_⟩
    have hhδ : (relativeFreeDeltaStructure S P.deltaStructure).IsDeltaHom E (h.comp j) :=
      hh.1.comp (pdCompletionUnit_isDeltaHom (relativeFreeDeltaStructure S P.deltaStructure) dB)
    obtain ⟨g', _, hu⟩ := existsUnique_relativeFreeDeltaHom P.deltaStructure E f hf a
    have hleft : h.comp j = g' := hu _ ⟨hhδ, ?_, hh.2.2⟩
    · have hright : raw = g' := hu _ ⟨rawδ, rawBase, fun s => relativeFreeDeltaEval_X E f a s 0⟩
      exact hleft.trans hright.symm
    · rw [RingHom.comp_assoc]
      exact hh.2.1

/-- 完備自由 δ 環は p について導来完備。 -/
theorem completedFreeDelta_complete_p :
    IsModuleComplete (completedFreeDelta P S) (p : completedFreeDelta P S)
      (ModuleCat.of _ (completedFreeDelta P S)) :=
  pdCompletionH0_self_complete_p B p dB

/-- 完備自由 δ 環は基底生成元の像について導来完備。 -/
theorem completedFreeDelta_complete_generator :
    IsModuleComplete (completedFreeDelta P S) (completedFreeDeltaBase P S P.generator)
      (ModuleCat.of _ (completedFreeDelta P S)) :=
  pdCompletionH0_self_complete_d B p dB

/-- 基底射と初期座標上で一致する二つの完備自由 δ 環の射は等しい。 -/
theorem completedFreeDeltaHom_ext {D : Type u} [CommRing D]
    (E : DeltaStructure p D) (f : A →+* D) (hf : P.deltaStructure.IsDeltaHom E f)
    (hp : IsModuleComplete D (p : D) (ModuleCat.of D D))
    (hd : IsModuleComplete D (f P.generator) (ModuleCat.of D D))
    {g g' : completedFreeDelta P S →+* D}
    (hg : (completedFreeDeltaStructure P S).IsDeltaHom E g)
    (hg' : (completedFreeDeltaStructure P S).IsDeltaHom E g')
    (hb : g.comp (completedFreeDeltaBase P S) = f)
    (hb' : g'.comp (completedFreeDeltaBase P S) = f)
    (hX : ∀ s, g (completedFreeDeltaVariable P S s) = g' (completedFreeDeltaVariable P S s)) :
    g = g' := by
  obtain ⟨_, _, h⟩ := existsUnique_completedFreeDeltaHom P S E f hf hp hd
    (fun s => g' (completedFreeDeltaVariable P S s))
  exact (h g ⟨hg, hb, hX⟩).trans (h g' ⟨hg', hb', fun _ => rfl⟩).symm

end SerrePositivity.BhattScholze.Prismatic
