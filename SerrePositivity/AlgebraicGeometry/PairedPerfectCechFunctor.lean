module

public import SerrePositivity.AlgebraicGeometry.PairedCechOpenNaturality
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechRefinedIdentity
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechRefinedComposition

/-!
概要：同じ積とタプル被覆の完全構造層の Čech 複体を、二変数の増大図式にする。
方針：既存の refinedPullback と単位・合成則へ、元の幾何的な射と位置写像を渡す。
規約：実際の係数・開・増大点・二つの方向の合成を保持する。
使われ方：複体値の二重 Čech と相対 fppf の比較（計画 P15〜P18）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- 同じ積の射による完全構造層の引き戻しを、元の二つのタプルの位置写像で細分する。 -/
def pairedPerfectCechMap {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    {a a' b b' : AugmentedSimplexCategory} (α : a ⟶ a') (β : b ⟶ b') :
    pairedPerfectCechComplex h g U V p hp hR a b ⟶
      pairedPerfectCechComplex h g U V p hp hR a' b' :=
  schemeStructurePerfectCechRefinedPullbackMap (pairedCechSchemeMap h g α β)
    p hp (pairedCechPrimeCast h g p hR a b) (pairedCechPrimeCast h g p hR a' b')
    (pairedCechOpen h g U V a b) (pairedCechOpen h g U V a' b')
    (fun t ↦ (t.1 ∘ augmentedTupleIndexMap α, t.2 ∘ augmentedTupleIndexMap β))
    (pairedCechOpen_map_le h g U V α β)

/-- 同じ二変数の引き戻しは、二つの恒等射を複体の恒等射へ送る。 -/
theorem pairedPerfectCechMap_id {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (a b : AugmentedSimplexCategory) :
    pairedPerfectCechMap h g U V p hp hR (𝟙 a) (𝟙 b) = 𝟙 _ := by
  exact schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq
    (pairedCechSchemeMap h g (𝟙 a) (𝟙 b)) (pairedCechSchemeMap_id h g a b)
    p hp (pairedCechPrimeCast h g p hR a b) (pairedCechOpen h g U V a b)
    (fun t ↦ (t.1 ∘ augmentedTupleIndexMap (𝟙 a), t.2 ∘ augmentedTupleIndexMap (𝟙 b)))
    (by funext t; simp only [augmentedTupleIndexMap_id, Function.comp_id]; rfl)
    (pairedCechOpen_map_le h g U V (𝟙 a) (𝟙 b))

/-- 元の二つの増大単体圏の合成は、同じ係数・細分の射の合成へ移る。 -/
theorem pairedPerfectCechMap_comp {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    {a a' a'' b b' b'' : AugmentedSimplexCategory}
    (α : a ⟶ a') (α' : a' ⟶ a'') (β : b ⟶ b') (β' : b' ⟶ b'') :
    pairedPerfectCechMap h g U V p hp hR (α ≫ α') (β ≫ β') =
      pairedPerfectCechMap h g U V p hp hR α β ≫
        pairedPerfectCechMap h g U V p hp hR α' β' := by
  let f := pairedCechSchemeMap h g α β
  let g' := pairedCechSchemeMap h g α' β'
  let k := pairedCechSchemeMap h g (α ≫ α') (β ≫ β')
  let ρ := fun t : (Fin (augmentedTupleLength a') → ι) × (Fin (augmentedTupleLength b') → κ) ↦
    (t.1 ∘ augmentedTupleIndexMap α, t.2 ∘ augmentedTupleIndexMap β)
  let σ := fun t : (Fin (augmentedTupleLength a'') → ι) × (Fin (augmentedTupleLength b'') → κ) ↦
    (t.1 ∘ augmentedTupleIndexMap α', t.2 ∘ augmentedTupleIndexMap β')
  let τ := fun t : (Fin (augmentedTupleLength a'') → ι) × (Fin (augmentedTupleLength b'') → κ) ↦
    (t.1 ∘ augmentedTupleIndexMap (α ≫ α'), t.2 ∘ augmentedTupleIndexMap (β ≫ β'))
  have hτ : τ = ρ ∘ σ := by
    funext t
    apply Prod.ext
    · exact congrArg (fun z ↦ t.1 ∘ z) (augmentedTupleIndexMap_comp α α')
    · exact congrArg (fun z ↦ t.2 ∘ z) (augmentedTupleIndexMap_comp β β')
  have hw : ∀ t, pairedCechOpen h g U V a'' b'' t ≤
      k ⁻¹ᵁ pairedCechOpen h g U V a b ((ρ ∘ σ) t) := by
    intro t
    rw [← hτ]
    exact pairedCechOpen_map_le h g U V (α ≫ α') (β ≫ β') t
  have hc := schemeStructurePerfectCechRefinedPullbackMap_compIndex
    f g' k (pairedCechSchemeMap_comp h g α α' β β').symm p hp
    (pairedCechPrimeCast h g p hR a b) (pairedCechPrimeCast h g p hR a' b')
    (pairedCechPrimeCast h g p hR a'' b'')
    (pairedCechOpen h g U V a b) (pairedCechOpen h g U V a' b')
    (pairedCechOpen h g U V a'' b'') ρ σ
    (pairedCechOpen_map_le h g U V α β) (pairedCechOpen_map_le h g U V α' β') hw
  have hL : pairedPerfectCechMap h g U V p hp hR (α ≫ α') (β ≫ β') =
      schemeStructurePerfectCechRefinedPullbackMap k p hp
        (pairedCechPrimeCast h g p hR a b) (pairedCechPrimeCast h g p hR a'' b'')
        (pairedCechOpen h g U V a b) (pairedCechOpen h g U V a'' b'') (ρ ∘ σ) hw := by
    unfold pairedPerfectCechMap
    congr 1
  exact hL.trans hc.symm

/-- 同じ積・タプル・実際の完全構造層の複体による二変数の増大 Čech 図式。 -/
def pairedPerfectCech {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ where
  obj a := pairedPerfectCechComplex h g U V p hp hR a.1 a.2
  map f := pairedPerfectCechMap h g U V p hp hR f.1 f.2
  map_id a := pairedPerfectCechMap_id h g U V p hp hR a.1 a.2
  map_comp f k := pairedPerfectCechMap_comp h g U V p hp hR f.1 k.1 f.2 k.2

end SerrePositivity.AlgebraicGeometry
