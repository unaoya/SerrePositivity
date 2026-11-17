module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Finset.Lattice.Fold

/-!
概要：同じ有限積の実際の Frobenius 順極限を、成分の順極限の積へ移す。
方針：各評価の環準同型を使い、有限段と冪零次数を有限の上界へそろえる。
規約：無限積との交換を主張せず、元の成分と写像を保持する。
使われ方：有限アフィン族の nerve と矩形タプルの係数の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {ι : Type} (A : ι → Type u) [∀ i, CommRing (A i)]
variable (p : ℕ) (hp : p.Prime) (hA : ∀ i, (p : A i) = 0)

/-- 同じ積環の標数条件は成分ごとの元の条件から得られる。 -/
theorem frobeniusPi_primeCast (hA : ∀ i, (p : A i) = 0) : (p : ∀ i, A i) = 0 := by
  funext i
  exact hA i

/-- 元の各評価の環準同型が誘導する実際の Frobenius 係数の写像。 -/
def frobeniusDirectLimitPiMap :
    FrobeniusDirectLimit (∀ i, A i) p hp (frobeniusPi_primeCast A p hA) →+*
      ∀ i, FrobeniusDirectLimit (A i) p hp (hA i) :=
  RingHom.pi (fun i ↦ frobeniusDirectLimitMap p hp
    (frobeniusPi_primeCast A p hA) (hA i) (Pi.evalRingHom A i))

/-- 同じ有限段の成分は、元の成分の同じ段に移る。 -/
theorem frobeniusDirectLimitPiMap_of (n : ℕ) (x : ∀ i, A i) (i : ι) :
    frobeniusDirectLimitPiMap A p hp hA
      (frobeniusDirectLimitOf (∀ i, A i) p hp (frobeniusPi_primeCast A p hA) n x) i =
        frobeniusDirectLimitOf (A i) p hp (hA i) n (x i) := rfl

/-- 同じ成分ごとの環の射を、実際の積の Frobenius 係数の比較は保つ。 -/
theorem frobeniusDirectLimitPiMap_naturality
    {B : ι → Type u} [∀ i, CommRing (B i)] (hB : ∀ i, (p : B i) = 0)
    (g : ∀ i, A i →+* B i)
    (z : FrobeniusDirectLimit (∀ i, A i) p hp (frobeniusPi_primeCast A p hA)) (i : ι) :
    frobeniusDirectLimitPiMap B p hp hB
      (frobeniusDirectLimitMap p hp (frobeniusPi_primeCast A p hA)
        (frobeniusPi_primeCast B p hB)
        (RingHom.pi (fun i ↦ (g i).comp (Pi.evalRingHom A i))) z) i =
      frobeniusDirectLimitMap p hp (hA i) (hB i) (g i)
        (frobeniusDirectLimitPiMap A p hp hA z i) := by
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (∀ i, A i) p hp (frobeniusPi_primeCast A p hA)) z
  rfl

/-- 添字を変える元の成分の環の射も、同じ Frobenius 係数の比較は保つ。 -/
theorem frobeniusDirectLimitPiMap_reindex_naturality
    {κ : Type} {B : κ → Type u} [∀ j, CommRing (B j)]
    (hB : ∀ j, (p : B j) = 0) (ρ : κ → ι) (g : ∀ j, A (ρ j) →+* B j)
    (z : FrobeniusDirectLimit (∀ i, A i) p hp (frobeniusPi_primeCast A p hA)) (j : κ) :
    frobeniusDirectLimitPiMap B p hp hB
      (frobeniusDirectLimitMap p hp (frobeniusPi_primeCast A p hA)
        (frobeniusPi_primeCast B p hB)
        (RingHom.pi (fun j ↦ (g j).comp (Pi.evalRingHom A (ρ j)))) z) j =
      frobeniusDirectLimitMap p hp (hA (ρ j)) (hB j) (g j)
        (frobeniusDirectLimitPiMap A p hp hA z (ρ j)) := by
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (∀ i, A i) p hp (frobeniusPi_primeCast A p hA)) z
  rfl

variable [Fintype ι]

/-- 同じ有限積の係数の比較は、成分の冪零次数の有限上界により単射。 -/
theorem frobeniusDirectLimitPiMap_injective :
    Function.Injective (frobeniusDirectLimitPiMap A p hp hA) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (∀ i, A i) p hp (frobeniusPi_primeCast A p hA)) z
  have hn (i : ι) : IsNilpotent (x i) :=
    (frobeniusDirectLimitOf_eq_zero_iff_nilpotent (A i) p hp (hA i) n (x i)).mp
      (congrFun hz i)
  choose e he using hn
  apply (frobeniusDirectLimitOf_eq_zero_iff_nilpotent
    (∀ i, A i) p hp (frobeniusPi_primeCast A p hA) n x).mpr
  refine ⟨Finset.univ.sup e, ?_⟩
  funext i
  exact pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (he i)

/-- 同じ有限積の係数の比較は、各元の有限段を同じ上界へそろえて全射。 -/
theorem frobeniusDirectLimitPiMap_surjective :
    Function.Surjective (frobeniusDirectLimitPiMap A p hp hA) := by
  classical
  intro z
  have hz (i : ι) : ∃ (n : ℕ) (x : A i),
      frobeniusDirectLimitOf (A i) p hp (hA i) n x = z i := by
    obtain ⟨n, x, hx⟩ := DirectLimit.exists_eq_mk
      (frobeniusDirectSystemMap (A i) p hp (hA i)) (z i)
    exact ⟨n, x, hx.symm⟩
  choose n x hx using hz
  let N := Finset.univ.sup n
  have hN (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨frobeniusDirectLimitOf (∀ i, A i) p hp (frobeniusPi_primeCast A p hA) N
    (fun i ↦ frobeniusDirectSystemMap (A i) p hp (hA i) (n i) N (hN i) (x i)), ?_⟩
  funext i
  rw [frobeniusDirectLimitPiMap_of]
  change DirectLimit.Ring.of (fun _ : ℕ ↦ A i)
      (frobeniusDirectSystemMap (A i) p hp (hA i)) N
      (frobeniusDirectSystemMap (A i) p hp (hA i) (n i) N (hN i) (x i)) = z i
  rw [DirectLimit.Ring.of_f]
  exact hx i

/-- 同じ有限積の Frobenius 係数の標準環同型。 -/
def frobeniusDirectLimitPiEquiv :
    FrobeniusDirectLimit (∀ i, A i) p hp (frobeniusPi_primeCast A p hA) ≃+*
      ∀ i, FrobeniusDirectLimit (A i) p hp (hA i) :=
  RingEquiv.ofBijective (frobeniusDirectLimitPiMap A p hp hA)
    ⟨frobeniusDirectLimitPiMap_injective A p hp hA,
      frobeniusDirectLimitPiMap_surjective A p hp hA⟩

end SerrePositivity.AlgebraicGeometry
