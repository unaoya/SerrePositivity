module

public import SerrePositivity.CategoryTheory.Limits
public import Mathlib.CategoryTheory.Action.Basic

/-!
# 対称列と各段の置換作用

対称列は有限集合と全単射の小さい亜群上の共変関手。
各段には対称群が作用し、対称列の射はその作用と両立する。
convolution は別に構成し、関手圏の点ごとのテンソル積とは区別する。
-/

@[expose] public section

universe v u

namespace SerrePositivity

open CategoryTheory

/-- C に値を取る対称列。 -/
def SymmetricSequence (C : Type u) [Category.{v} C] := FiniteBijection ⥤ C

namespace SymmetricSequence

variable {C : Type u} [Category.{v} C]

/-- 射は自然変換。点ごとのモノイダル構造はこの型には登録しない。 -/
instance : Category.{v} (SymmetricSequence C) :=
  inferInstanceAs (Category.{v} (FiniteBijection ⥤ C))

/-- 対称列を元の関手圏へ戻す、恒等的な包含。 -/
def toFunctorCategory : SymmetricSequence C ⥤ (FiniteBijection ⥤ C) where
  obj F := F
  map η := η

/-- 元の関手圏から対称列の型へ戻す恒等的な関手。 -/
def fromFunctorCategory : (FiniteBijection ⥤ C) ⥤ SymmetricSequence C where
  obj F := F
  map η := η

instance : (toFunctorCategory (C := C)).Full where
  map_surjective η := ⟨η, rfl⟩

instance : (toFunctorCategory (C := C)).Faithful where
  map_injective h := h

/-- 対称列の第 n 段。 -/
def level (F : SymmetricSequence C) (n : ℕ) : C := F.obj (FiniteBijection.of n)

/-- 第 n 段の対称群の作用。 -/
def levelAction (F : SymmetricSequence C) (n : ℕ) : Action C (Equiv.Perm (Fin n)) where
  V := level F n
  ρ := {
    toFun σ := End.of (F.map (FiniteBijection.permutation n σ))
    map_one' := by
      apply End.ext
      change F.map (FiniteBijection.permutation n 1) = 𝟙 _
      rw [FiniteBijection.permutation_one]
      exact F.map_id _
    map_mul' σ τ := by
      apply End.ext
      change F.map (FiniteBijection.permutation n (σ * τ)) =
        F.map (FiniteBijection.permutation n τ) ≫ F.map (FiniteBijection.permutation n σ)
      rw [FiniteBijection.permutation_mul, F.map_comp] }

/-- 作用の基礎となる射は、置換を対称列で写したもの。 -/
@[simp] lemma levelAction_ρ (F : SymmetricSequence C) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((levelAction F n).ρ σ).asHom = F.map (FiniteBijection.permutation n σ) := rfl

/-- 各段の作用への評価は、対称列の射を同変射へ送る。 -/
def levelActionFunctor (n : ℕ) : SymmetricSequence C ⥤ Action C (Equiv.Perm (Fin n)) where
  obj F := levelAction F n
  map η := {
    hom := η.app (FiniteBijection.of n)
    comm σ := η.naturality (FiniteBijection.permutation n σ) }
  map_id F := by apply Action.Hom.ext; rfl
  map_comp η θ := by apply Action.Hom.ext; rfl

/-- 対称列の射は各段の射で決まる。 -/
@[ext] lemma hom_ext {F G : SymmetricSequence C} (η θ : F ⟶ G)
    (h : ∀ n, η.app (FiniteBijection.of n) = θ.app (FiniteBijection.of n)) : η = θ := by
  apply NatTrans.ext
  funext X
  have hx := h (FiniteBijection.card X)
  rw [FiniteBijection.of_card X] at hx
  exact hx

/-- 置換は各段の同型に送られる。 -/
instance permutation_map_isIso (F : SymmetricSequence C) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) : IsIso (F.map (FiniteBijection.permutation n σ)) := by
  let F' : FiniteBijection ⥤ C := F
  change IsIso (F'.map (FiniteBijection.permutation n σ))
  infer_instance

end SymmetricSequence
end SerrePositivity
