module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedNormalizedPointed

/-! # 正規化した pinched 単体を区間との積へ引き戻す錐写像

概要：区間の零端を新しい零頂点へ潰し、一端を元の頂点の後者へ送る。
方針：各次数の単調写像を点ごとに定義し、全ての引き戻しとの可換性を照合する。
規約：欠けた頂点は非零の後者として欠けたまま。使われ方：相対ホモトピーの prism。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 区間パラメータで零頂点または元の頂点の後者を選ぶ単調写像。 -/
def pinchedConeIntervalOrderHom {d n : ℕ} (σ : Fin (d + 1) →o Fin (n + 1))
    (t : Fin (d + 1) →o Fin 2) : Fin (d + 1) →o Fin (n + 2) where
  toFun r := if t r = 0 then 0 else (σ r).succ
  monotone' a b hab := by
    dsimp
    split_ifs with ha hb hb
    · exact le_rfl
    · exact Fin.zero_le _
    · exfalso
      apply ha
      exact le_antisymm (by simpa only [hb] using t.monotone hab) (Fin.zero_le _)
    · exact Fin.succ_le_succ_iff.mpr (σ.monotone hab)

/-- 区間との積から一段高い標準単体への実単体的写像。 -/
def pinchedConeIntervalMap (n : ℕ) : (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[n + 1] where
  app m := ↾fun p => ULift.up (SimplexCategory.mkHom
    (pinchedConeIntervalOrderHom p.1.down.toOrderHom p.2.down.toOrderHom))
  naturality {m k} α := by
    apply ConcreteCategory.hom_ext
    intro p
    apply SSet.stdSimplex.ext
    intro r
    rfl

/-- 錐写像の各頂点の値。 -/
lemma pinchedConeIntervalMap_apply {d n : ℕ} (σ : (Δ[n] : SSet.{u}) _⦋d⦌)
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (r : Fin (d + 1)) :
    ((pinchedConeIntervalMap n).app _ (σ, t)) r =
      if t r = 0 then 0 else (σ r).succ := rfl

/-- 元の単体が欠く頂点の後者は、錐写像の像からも欠ける。 -/
lemma pinchedConeIntervalOrderHom_avoids {d n : ℕ}
    (σ : Fin (d + 1) →o Fin (n + 1)) (t : Fin (d + 1) →o Fin 2)
    (j : Fin (n + 1)) (hj : ∀ r, σ r ≠ j) :
    ∀ r, pinchedConeIntervalOrderHom σ t r ≠ j.succ := by
  intro r
  dsimp [pinchedConeIntervalOrderHom]
  split_ifs
  · exact fun h => Fin.succ_ne_zero j h.symm
  · exact fun h => hj r (Fin.succ_inj.mp h)

/-- 区間の零端は、新しい零頂点の定値写像。 -/
lemma pinchedConeIntervalMap_zero (n : ℕ) :
    SSet.ι₀ ≫ pinchedConeIntervalMap.{u} n =
      SSet.stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋n + 1⦌ 0) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro σ
  apply SSet.stdSimplex.ext
  intro r
  rfl

/-- 区間の一端は、零面の標準包含。 -/
lemma pinchedConeIntervalMap_one (n : ℕ) :
    SSet.ι₁ ≫ pinchedConeIntervalMap.{u} n = SSet.stdSimplex.δ 0 := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro σ
  apply SSet.stdSimplex.ext
  intro r
  change (if (1 : Fin 2) = 0 then 0 else (σ.down.toOrderHom r).succ) = _
  simp
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
