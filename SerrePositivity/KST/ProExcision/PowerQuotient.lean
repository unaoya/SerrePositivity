module

public import SerrePositivity.KST.ProExcision.ScalarConeBiTower

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# 動く加群の冪商と pro 同型

概要：加群の塔の pro 同型を、段 n ごとに aⁿ で割った塔へ移す。
方針：eventual 逆射を大きい冪商から小さい冪商へ降ろす。
規約：スカラー商の冪指数と係数の添字が同時に動く。
使われ方：KST Lemma 4.10 の列長帰納法における短い列の比較の保存。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

/-- 概要：線形写像を大きい冪商から小さい冪商へ降ろす。
方針：スカラー像の包含を使う通常の商写像。
規約：n≤m。使われ方：KST Lemma 4.10 の pro 逆射の商への降下。 -/
def powerQuotientMap (a : R) {M N : ModuleCat.{u} R} {m n : ℕ} (h : n ≤ m) (f : M ⟶ N) :
    (scalarQuotientFunctor (a ^ m)).obj M ⟶ (scalarQuotientFunctor (a ^ n)).obj N :=
  ModuleCat.ofHom (Submodule.mapQ _ _ f.hom (powerScalarRange_map a f h))

/-- 概要：冪商上の写像の合成は元の線形写像の合成を誘導する。
方針：通常商の代表元で確認する。
規約：各指数の順序を明示する。使われ方：KST Lemma 4.10 の eventual 逆射の二つの三角形。 -/
theorem powerQuotientMap_comp (a : R) {M N P : ModuleCat.{u} R}
    {k m n : ℕ} (hm : m ≤ k) (hn : n ≤ m) (f : M ⟶ N) (g : N ⟶ P) :
    powerQuotientMap a hm f ≫ powerQuotientMap a hn g =
      powerQuotientMap a (hn.trans hm) (f ≫ g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

/-- 概要：動く加群の n 段を aⁿ で割る塔。
方針：元の係数遷移を、異なる冪商間へ降ろす。
規約：冪指数零の商も含む。使われ方：KST Lemma 4.10 の通常商の列長帰納。 -/
def Tower.powerQuotient (X : Tower (ModuleCat.{u} R)) (a : R) : Tower (ModuleCat.{u} R) where
  obj n := (scalarQuotientFunctor (a ^ n)).obj (X.obj n)
  transition h := powerQuotientMap a h (X.transition h)
  transition_self n := by
    simp only [X.transition_self]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  transition_comp hm hn := by rw [powerQuotientMap_comp, X.transition_comp]

/-- 概要：係数のレベル射を段ごとの冪商へ降ろす。
方針：同じ指数で商写像を誘導し、元の自然性を使う。
規約：左右で同じ a を使用。使われ方：KST Lemma 4.10 の比較射の反復。 -/
def LevelHom.powerQuotient {X Y : Tower (ModuleCat.{u} R)} (f : LevelHom X Y) (a : R) :
    LevelHom (X.powerQuotient a) (Y.powerQuotient a) where
  app n := powerQuotientMap a (le_refl n) (f.app n)
  naturality {m n} h := by
    change powerQuotientMap a h (X.transition h) ≫ powerQuotientMap a _ (f.app n) =
      powerQuotientMap a _ (f.app m) ≫ powerQuotientMap a h (Y.transition h)
    rw [powerQuotientMap_comp, powerQuotientMap_comp, f.naturality]

/-- 概要：pro 同型は、係数と同じ添字で冪商をとっても pro 同型。
方針：R 線形な eventual 逆射を冪商へ降ろし、その二つの三角形を商へ写す。
規約：固定された関手による保存だけではなく、動く冪指数を扱う。
使われ方：KST Lemma 4.10 の列長帰納法での短い列の比較の保存。 -/
theorem IsProIso.powerQuotient {X Y : Tower (ModuleCat.{u} R)} {f : LevelHom X Y}
    (hf : IsProIso f) (a : R) : IsProIso (f.powerQuotient a) := by
  intro n
  obtain ⟨m, h, g, hg, gh⟩ := hf n
  refine ⟨m, h, powerQuotientMap a h g, ?_, ?_⟩
  · change powerQuotientMap a (le_refl m) (f.app m) ≫ powerQuotientMap a h g =
      powerQuotientMap a h (X.transition h)
    rw [powerQuotientMap_comp, hg]
  · change powerQuotientMap a h g ≫ powerQuotientMap a (le_refl n) (f.app n) =
      powerQuotientMap a h (Y.transition h)
    rw [powerQuotientMap_comp, gh]

end SerrePositivity.KST.ProExcision
