module

public import SerrePositivity.AlgebraicGeometry.AffineBlowupFlatBaseChange
public import SerrePositivity.AlgebraicGeometry.AffineEtaleCenterProduct
public import SerrePositivity.AlgebraicGeometry.BlowupFunctor
public import SerrePositivity.AlgebraicGeometry.ProductBlowup
public import SerrePositivity.AlgebraicGeometry.StandardEtaleCenterDescent
public import Mathlib.RingTheory.Flat.Localization

/-!
概要：有限個の étale 局所中心を、アフィン基底の一つのブローアップで支配する。
方針：共通中心を各チャートに引き戻し、積中心から局所中心への比較射を使う。
規約：個別の局所中心が基底から降りる中心の因子になることを入力する。
使われ方：各局所中心の純変換の平坦性を、同じ基底ブローアップで確かめる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

/--
概要：有限個の平坦なアフィンチャート上で局所中心が基底中心の因子になるなら、
一つの基底ブローアップの底変換がすべての局所ブローアップを支配する。
方針：共通中心の積を取り、平坦底変換との比較同型を積中心の比較射と合成する。
規約：各中心は境界元の冪を含む。比較射は各チャートの基底上の射として与える。
使われ方：Stacks 0814 の局所中心を基底の一つのブローアップで支配する段階。
-/
theorem exists_common_affineBlowup_refinement_of_factors
    {R ι : Type u} [CommRing R] [IsNoetherianRing R] [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] [∀ i, Module.Flat R (B i)]
    (J : ∀ i, Ideal (B i)) (a : R)
    (h : ∀ i, ∃ (I : Ideal R) (n : ℕ), a ^ n ∈ I ∧
      ∃ K : Ideal (B i), K.FG ∧ I.map (algebraMap R (B i)) = J i * K) :
    ∃ I : Ideal R, I.FG ∧ (∃ n : ℕ, a ^ n ∈ I) ∧
      ∀ i, let f := Spec.map (CommRingCat.ofHom (algebraMap R (B i)))
        ∃ p : pullback (affineBlowupπ I) f ⟶ affineBlowup (J i),
          p ≫ affineBlowupπ (J i) = pullback.snd (affineBlowupπ I) f := by
  obtain ⟨I, hI, ha, hprod⟩ :=
    exists_common_affine_center_of_factors B (fun i => algebraMap R (B i)) J a h
  refine ⟨I, hI, ha, fun i => ?_⟩
  obtain ⟨K, _, hK⟩ := hprod i
  let e := (isPullback_affineBlowupBaseMap_of_flat (S := B i) I).isoPullback
  let p := e.inv ≫ eqToHom (congrArg affineBlowup hK) ≫ affineBlowupProductLeftMap (J i) K
  refine ⟨p, ?_⟩
  simp only [p, Category.assoc, affineBlowupProductLeftMap_base]
  rw [show eqToHom (congrArg affineBlowup hK) ≫ affineBlowupπ (J i * K) =
    affineBlowupπ (I.map (algebraMap R (B i))) from affineBlowup_eqToHom_base _ _ hK]
  exact (isPullback_affineBlowupBaseMap_of_flat (S := B i) I).isoPullback_inv_snd


/--
概要：有限個の étale アフィン上の許容ブローアップは、主開被覆上で一つの基底ブローアップに支配される。
方針：各中心の因子分解が成り立つ主開を有限個選び、全チャートの中心を一つの積にまとめる。
規約：境界元は基底で一つ選び、各局所中心はその像のある冪を含む。
使われ方：Stacks 0814 で、一つの基底ブローアップ上の局所純変換の平坦性を得る。
-/
theorem exists_common_affineBlowup_refinement_of_etale_centers
    {R ι : Type u} [CommRing R] [IsNoetherianRing R] [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Algebra.Etale R (B i)] (J : ∀ i, Ideal (B i)) (a : R)
    (h : ∀ i, ∃ k : ℕ, algebraMap R (B i) (a ^ k) ∈ J i) :
    ∃ I : Ideal R, I.FG ∧ (∃ n : ℕ, a ^ n ∈ I) ∧
      ∀ i, ∃ s : Finset (B i), Ideal.span (s : Set (B i)) = ⊤ ∧
        ∀ b : s, let L := Localization.Away b.1
          let f := Spec.map (CommRingCat.ofHom (algebraMap R L))
          ∃ p : pullback (affineBlowupπ I) f ⟶ affineBlowup (J i),
            p ≫ affineBlowupπ (J i) =
              pullback.snd (affineBlowupπ I) f ≫
                Spec.map (CommRingCat.ofHom (algebraMap (B i) L)) := by
  have hcover (i : ι) :
      ∃ s : Finset (B i), Ideal.span (s : Set (B i)) = ⊤ ∧
        ∀ b ∈ s, ∃ (I : Ideal R) (n : ℕ), a ^ n ∈ I ∧
          ∃ K : Ideal (Localization.Away b), K.FG ∧
            I.map (algebraMap R (Localization.Away b)) =
              (J i).map (algebraMap (B i) (Localization.Away b)) * K := by
    obtain ⟨k, hk⟩ := h i
    exact exists_finset_away_center_factor_cover (J i) a k hk
  choose s hs hfactor using hcover
  let σ := Σ i, {b : B i // b ∈ s i}
  let D (j : σ) := Localization.Away j.2.1
  let K (j : σ) := (J j.1).map (algebraMap (B j.1) (D j))
  let : ∀ j : σ, Module.Flat R (D j) := fun j => by
    let : Module.Flat (B j.1) (D j) := IsLocalization.flat (D j) (Submonoid.powers j.2.1)
    exact Module.Flat.trans R (B j.1) (D j)
  obtain ⟨I, hI, ha, hmaps⟩ :=
    exists_common_affineBlowup_refinement_of_factors D K a (fun j => hfactor j.1 j.2.1 j.2.2)
  refine ⟨I, hI, ha, fun i => ⟨s i, hs i, fun b => ?_⟩⟩
  let j : σ := ⟨i, b⟩
  obtain ⟨p, hp⟩ := hmaps j
  let f := algebraMap (B i) (D j)
  refine ⟨p ≫ affineBlowupBaseMap (J i) f, ?_⟩
  rw [Category.assoc, affineBlowupBaseMap_base, ← Category.assoc, hp]

end SerrePositivity.AlgebraicGeometry
