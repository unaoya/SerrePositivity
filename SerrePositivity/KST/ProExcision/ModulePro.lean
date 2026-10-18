module

public import SerrePositivity.KST.ProExcision.Pro
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

/-!
# 加群の塔の eventual 単射・全射

概要：核と余核の eventual 零化を Artin–Mazur 判定と結ぶ。
方針：核を消す遷移を像上に降ろし、もう一段の遷移と合成する。
規約：加群の元の持ち上げに線形な切断の存在を要求しない。
使われ方：正本 §2.6 L2、KST §4.1 の pro 五項補題。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory

variable {R : Type u} [Ring R]

/-- 概要：遷移の合成律を元に適用する。方針：射の等式を評価する。
規約：加群圏の線形写像で評価。使われ方：KST §4.1 の diagram chase。 -/
theorem Tower.transition_apply (X : Tower (ModuleCat.{u} R))
    {k m n : ℕ} (hm : m ≤ k) (hn : n ≤ m) (x : X.obj k) :
    (X.transition hn).hom ((X.transition hm).hom x) =
      (X.transition (hn.trans hm)).hom x :=
  congrArg (fun f ↦ f.hom x) (X.transition_comp hm hn)

/-- 概要：レベル射の自然性を元に適用する。方針：可換四角形を評価する。
規約：大きい段から小さい段へ進む。使われ方：KST §4.1 の diagram chase。 -/
theorem LevelHom.naturality_apply {X Y : Tower (ModuleCat.{u} R)}
    (f : LevelHom X Y) {m n : ℕ} (h : n ≤ m) (x : X.obj m) :
    (f.app n).hom ((X.transition h).hom x) =
      (Y.transition h).hom ((f.app m).hom x) :=
  congrArg (fun g ↦ g.hom x) (f.naturality h)

/-- 概要：レベル射の核の pro-零性。方針：核の元を遷移で一様に零化する。
規約：指数は元に依存しない。使われ方：正本 §2.6 L2 の単射側。 -/
def IsProMono {X Y : Tower (ModuleCat.{u} R)} (f : LevelHom X Y) : Prop :=
  ∀ n, ∃ m, ∃ h : n ≤ m, ∀ x : X.obj m,
    (f.app m).hom x = 0 → (X.transition h).hom x = 0

/-- 概要：レベル射の余核の pro-零性。方針：遷移の像を射の像へ含める。
規約：持ち上げは元ごとに存在すればよい。使われ方：正本 §2.6 L2 の全射側。 -/
def IsProEpi {X Y : Tower (ModuleCat.{u} R)} (f : LevelHom X Y) : Prop :=
  ∀ n, ∃ m, ∃ h : n ≤ m, ∀ y : Y.obj m,
    ∃ x : X.obj n, (f.app n).hom x = (Y.transition h).hom y

/-- 概要：pro 同型の核は pro-零。方針：逆射を核の元へ適用する。
規約：Artin–Mazur 判定の第一三角形を使用。
使われ方：KST §4.1 の pro 五項補題。 -/
theorem IsProIso.isProMono {X Y : Tower (ModuleCat.{u} R)}
    {f : LevelHom X Y} (hf : IsProIso f) : IsProMono f := by
  intro n
  obtain ⟨m, h, g, hg, _⟩ := hf n
  refine ⟨m, h, fun x hx ↦ ?_⟩
  have hh := congrArg (fun k ↦ k.hom x) hg
  change g.hom ((f.app m).hom x) = (X.transition h).hom x at hh
  rw [hx, map_zero] at hh
  exact hh.symm

/-- 概要：pro 同型の余核は pro-零。方針：逆射を持ち上げとして使う。
規約：Artin–Mazur 判定の第二三角形を使用。
使われ方：KST §4.1 の pro 五項補題。 -/
theorem IsProIso.isProEpi {X Y : Tower (ModuleCat.{u} R)}
    {f : LevelHom X Y} (hf : IsProIso f) : IsProEpi f := by
  intro n
  obtain ⟨m, h, g, _, gh⟩ := hf n
  exact ⟨m, h, fun y ↦ ⟨g.hom y, congrArg (fun k ↦ k.hom y) gh⟩⟩

/-- 概要：核を消す線形写像を元の写像の像上へ降ろす。
方針：核による商と像の第一同型定理を使う。
規約：加群の分裂性は要求しない。使われ方：pro 同型判定の逆向き。 -/
noncomputable def descendRange {A B C : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : A →ₗ[R] C)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : LinearMap.range f →ₗ[R] C :=
  ((LinearMap.ker f).liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap

/-- 概要：像へ降ろした写像の値。方針：商と像の比較の計算則を使う。
規約：像の所属証明の選択に依存しない。使われ方：eventual 逆射の二つの三角形。 -/
theorem descendRange_apply {A B C : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : A →ₗ[R] C)
    (h : LinearMap.ker f ≤ LinearMap.ker g) (x : A)
    (hx : f x ∈ LinearMap.range f) : descendRange f g h ⟨f x, hx⟩ = g x := by
  simp [descendRange]

/-- 概要：核・余核の pro-零性から Artin–Mazur 型 pro 同型判定を得る。
方針：核を消す遷移を像へ降ろし、像に入る次の遷移を前合成する。
規約：元の持ち上げの線形性は仮定しない。
使われ方：正本 §2.6 L2 の pro 五項補題。 -/
theorem isProIso_of_mono_epi {X Y : Tower (ModuleCat.{u} R)}
    {f : LevelHom X Y} (hm : IsProMono f) (he : IsProEpi f) : IsProIso f := by
  classical
  intro n
  obtain ⟨s, hns, hs⟩ := hm n
  obtain ⟨t, hst, ht⟩ := he s
  let a := (f.app s).hom
  let b := (X.transition hns).hom
  have hab : LinearMap.ker a ≤ LinearMap.ker b := by
    intro x hx
    exact hs x hx
  let q : Y.obj t →ₗ[R] LinearMap.range a :=
    (Y.transition hst).hom.codRestrict (LinearMap.range a) (fun y ↦ by
      obtain ⟨x, hx⟩ := ht y
      exact ⟨x, hx⟩)
  let g := (descendRange a b hab).comp q
  have value (y : Y.obj t) (x : X.obj s)
      (hx : a x = (Y.transition hst).hom y) : g y = b x := by
    change descendRange a b hab (q y) = b x
    have hq : q y = ⟨a x, LinearMap.mem_range.mpr ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
    rw [hq]
    exact descendRange_apply a b hab x _
  refine ⟨t, hns.trans hst, ModuleCat.ofHom g, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change g ((f.app t).hom x) = (X.transition (hns.trans hst)).hom x
    rw [value _ ((X.transition hst).hom x) (f.naturality_apply hst x)]
    exact X.transition_apply hst hns x
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    obtain ⟨x, hx⟩ := ht y
    change (f.app n).hom (g y) = (Y.transition (hns.trans hst)).hom y
    rw [value y x hx, f.naturality_apply hns x, hx]
    exact Y.transition_apply hst hns y

end SerrePositivity.KST.ProExcision
