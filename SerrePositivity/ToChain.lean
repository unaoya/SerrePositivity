module

public import SerrePositivity.Koszul
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.Additive

/-!
# ℤ 添字 cochain 複体の ℕ 添字 chain 複体への制限

埋め込み `n ↦ -n`（`ComplexShape.embeddingUpIntLE 0`）に沿った制限 `toChain K`。
`K` が `0` 以下の次数に乗るとき、ホモロジーは保たれる：

- `toChainHomologyIsoSucc`：`n ≥ 1` で `(toChain K).homology n ≅ K.homology (-n)`
  （Mathlib の `restrictionHomologyIso`）。
- `toChainHomologyIsoZero`：`K.X i = 0 (i > 0)` なら `(toChain K).homology 0 ≅ K.homology 0`。
  どちらも `opcycles` と同型なので、`restrictionOpcyclesIso` を経由する。
- `toChainHomologyIso`：両者をまとめたもの。
- `mapRestrictionIso`：加法的関手は制限と両立する。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 埋め込み `down ℕ → up ℤ`、`n ↦ -n`。 -/
noncomputable abbrev embUp : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpIntLE 0

instance : embUp.IsRelIff := inferInstanceAs (ComplexShape.embeddingUpIntLE 0).IsRelIff

/-- ℤ 添字の cochain 複体の、`n ↦ -n` に沿った ℕ 添字の chain 複体への制限。 -/
noncomputable abbrev toChain (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  K.restriction embUp

section toChain

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- `n ≥ 1` でのホモロジーの同型。 -/
noncomputable def toChainHomologyIsoSucc (n : ℕ) :
    (toChain K).homology (n + 1) ≅ K.homology (-(n + 1 : ℕ) : ℤ) :=
  HomologicalComplex.restrictionHomologyIso K embUp (n + 2) (n + 1) n
    (hi := by simp [ChainComplex.prev]) (hk := ChainComplex.next_nat_succ n)
    (i' := -(n + 2 : ℕ)) (j' := -(n + 1 : ℕ)) (k' := -(n : ℕ))
    (hi' := by simp) (hj' := by simp) (hk' := by simp)
    (hi'' := by rw [CochainComplex.prev]; omega) (hk'' := by rw [CochainComplex.next]; omega)

/-- `K.X 1 = 0` なら `K.d 0 1 = 0`。 -/
lemma d_zero_one_eq_zero (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) : K.d 0 1 = 0 :=
  (hK 1 one_pos).eq_of_tgt _ _

/-- `K.X 1 = 0` のとき、`0` 次のホモロジーの同型。 -/
noncomputable def toChainHomologyIsoZero (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) :
    (toChain K).homology 0 ≅ K.homology 0 :=
  haveI : IsIso (K.homologyι 0) :=
    K.isIso_homologyι 0 1 (by simp [CochainComplex.next]) (d_zero_one_eq_zero K hK)
  asIso ((toChain K).homologyι 0) ≪≫
    HomologicalComplex.restrictionOpcyclesIso K embUp (i := 1) (j := 0)
      (hi := by simp [ChainComplex.prev]) (i' := -1) (j' := 0) (hi' := by simp) (hj' := by simp)
      (hi'' := by rw [CochainComplex.prev]; omega) ≪≫
    (asIso (K.homologyι 0)).symm

/-- `K.X i = 0 (i > 0)` のとき、すべての `n` で `(toChain K).homology n ≅ K.homology (-n)`。 -/
noncomputable def toChainHomologyIso (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) :
    ∀ n : ℕ, (toChain K).homology n ≅ K.homology (-(n : ℤ))
  | 0 => toChainHomologyIsoZero K hK ≪≫ eqToIso (by simp)
  | n + 1 => toChainHomologyIsoSucc K n

end toChain

/-- 加法的関手は `n ↦ -n` に沿った制限と両立する（各項・各微分は定義上同じ）。 -/
noncomputable def mapRestrictionIso {S : Type u} [CommRing S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (F.mapHomologicalComplex _).obj (toChain K) ≅ toChain ((F.mapHomologicalComplex _).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
    (fun _ _ _ ↦ (Category.id_comp _).trans (Category.comp_id _).symm)

end SerrePositivity
