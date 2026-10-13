module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # 代数図式の添字変更と制限

単調な添字写像による引き戻し。自己・合成則、局所性、指定終域への両立を保持し、
二回の制限と合成した添字による制限が同じ遷移写像になることを確認する。
-/

@[expose] public section
namespace SerrePositivity
variable {B ι κ : Type*} [CommRing B] [Preorder ι] [Preorder κ]
variable (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
variable (f : ∀ i j, i ≤ j → S i →ₐ[B] S j)
variable (r : κ → ι) (hr : Monotone r)

/-- 添字が等しければ、源と終域の型も含めて遷移写像が一致する。
順序の証明引数は証明無関係性で同一視される。 -/
theorem algebraSystemMap_heq_of_eq {i j i' j' : ι}
    (hi : i = i') (hj : j = j') (h : i ≤ j) (h' : i' ≤ j') :
    HEq (f i j h) (f i' j' h') := by
  cases hi
  cases hj
  rfl

/-- 単調な添字写像に沿って遷移写像を引き戻す。 -/
def algebraSystemReindexMap : ∀ i j, i ≤ j → S (r i) →ₐ[B] S (r j) :=
  fun i j h ↦ f (r i) (r j) (hr h)

/-- 有向図式の法則は添字変更で保持される。添字写像の単射性は不要。 -/
theorem algebraSystemReindex_directedSystem [DirectedSystem S (f · · ·)] :
    DirectedSystem (fun i ↦ S (r i)) (algebraSystemReindexMap S f r hr · · ·) := by
  constructor
  · intro i x
    exact DirectedSystem.map_self' (f := f) x
  · intro k j i hij hjk x
    exact DirectedSystem.map_map' (f := f) (hr hij) (hr hjk) x

/-- 局所な遷移写像は制限しても局所である。 -/
theorem algebraSystemReindex_isLocalHom
    (hf : ∀ i j h, IsLocalHom (f i j h).toRingHom) :
    ∀ i j h, IsLocalHom (algebraSystemReindexMap S f r hr i j h).toRingHom :=
  fun i j h ↦ hf (r i) (r j) (hr h)

/-- 恒等添字での制限は元の遷移写像である。 -/
theorem algebraSystemReindexMap_id :
    algebraSystemReindexMap S f id monotone_id = f := rfl

/-- 二回の制限は、添字写像を合成した一回の制限と同じ。
証明引数の違いにもかかわらず、遷移写像は定義的に一致する。 -/
theorem algebraSystemReindexMap_comp {J : Type*} [Preorder J]
    (s : J → κ) (hs : Monotone s) :
    algebraSystemReindexMap (fun j ↦ S (r j)) (algebraSystemReindexMap S f r hr) s hs =
      algebraSystemReindexMap S f (r ∘ s) (hr.comp hs) := rfl

section Target
variable {K : Type*} [CommRing K] [Algebra B K]
variable (g : ∀ i, S i →ₐ[B] K)
variable (hg : ∀ i j h x, g j (f i j h x) = g i x)

omit [Preorder ι] in
/-- 源の添字が等しければ、指定終域への写像も型の同一視を含めて一致する。 -/
theorem algebraSystemTarget_heq_of_eq {i j : ι} (h : i = j) : HEq (g i) (g j) := by
  cases h
  rfl

include hg in
/-- 指定終域への写像の両立は制限で保持される。 -/
theorem algebraSystemReindexTarget_compatible :
    ∀ i j h x, g (r j) (algebraSystemReindexMap S f r hr i j h x) = g (r i) x :=
  fun i j h x ↦ hg (r i) (r j) (hr h) x

end Target
end SerrePositivity
