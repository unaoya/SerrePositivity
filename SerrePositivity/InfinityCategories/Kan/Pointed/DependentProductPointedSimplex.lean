module

public import SerrePositivity.InfinityCategories.Kan.SimplicialDependentProduct

/-!
概要：関数複体の境界定数単体と関係充填を座標ごとに構成する。
方針：単体と RelStruct の充填射を関数複体への lift で束ねる。
規約：座標ごとの基点と同じ面添字を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3。cochain の関数空間のホモトピー群。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SimplicialDependentProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type u} {X : S → SSet.{u}} {n : ℕ} {b : ∀ s, (X s) _⦋0⦌}

/-- 概要：各座標の境界定数単体を関数複体の境界定数単体へ束ねる。
方針：充填射を lift し、境界の式を各評価で検査する。
規約：基点は指定した基点の関数。
使われ方：Goerss–Jardine I §7。関数複体のホモトピー類の代表。 -/
def simplex (f : ∀ s, (X s).PtSimplex n (b s)) : (obj S X).PtSimplex n b where
  map := lift (fun s ↦ (f s).map)
  comm := by
    apply hom_ext
    intro s
    rw [Category.assoc, lift_eval]
    change (boundary n).ι ≫ (f s).map = SSet.const (b s)
    simp

lemma eval_simplex (f : ∀ s, (X s).PtSimplex n (b s)) (s : S) :
    mapSimplex (eval S X s) rfl (simplex f) = f s := by
  apply RelativeMorphism.ext
  exact lift_eval _ s

/-- 概要：各評価での関係充填を関数複体の一つの関係充填へ束ねる。
方針：全ての面の式を各評価で確認する。
規約：全ての座標で同じ面添字を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3。関数複体のホモトピー類の識別。 -/
def relStruct {f g : (obj S X).PtSimplex n b} {i : Fin (n + 1)}
    (r : ∀ s, PtSimplex.RelStruct (mapSimplex (eval S X s) rfl f)
      (mapSimplex (eval S X s) rfl g) i) : PtSimplex.RelStruct f g i where
  map := lift (fun s ↦ (r s).map)
  δ_castSucc_map := by
    apply hom_ext
    intro s
    rw [Category.assoc, lift_eval]
    exact (r s).δ_castSucc_map
  δ_succ_map := by
    apply hom_ext
    intro s
    rw [Category.assoc, lift_eval]
    exact (r s).δ_succ_map
  δ_map_of_lt j hj := by
    apply hom_ext
    intro s
    rw [Category.assoc, lift_eval, SSet.const_comp]
    exact (r s).δ_map_of_lt j hj
  δ_map_of_gt j hj := by
    apply hom_ext
    intro s
    rw [Category.assoc, lift_eval, SSet.const_comp]
    exact (r s).δ_map_of_gt j hj

end

end SerrePositivity.KST.Spectra.SimplicialDependentProduct
