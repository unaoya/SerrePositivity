module

public import SerrePositivity.AlgebraicGeometry.AffineBlowupFlatBaseChange
public import SerrePositivity.AlgebraicGeometry.AffineEtaleCenterProduct
public import SerrePositivity.AlgebraicGeometry.ProductBlowup

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

end SerrePositivity.AlgebraicGeometry
