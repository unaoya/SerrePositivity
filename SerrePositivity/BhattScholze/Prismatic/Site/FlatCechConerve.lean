module

public import SerrePositivity.BhattScholze.Prismatic.Site.FlatTopologyPushout
public import SerrePositivity.CategoryTheory.FiniteWidePushout

/-!
# 平坦な被覆の完備 Čech 余脈体

## 概要
prismatic site の完備押し出しを反復して、平坦な被覆の増大付き余脈体を作る。

## 方針
各有限広押し出しに必要な二項押し出しを、平坦な被覆の底変換から得る。

## 規約
BS 著者版 Corollary 3.12 (c)。環の向きで余脈体を取る。

## 使われ方
有限剰余の通常の Čech 複体との比較。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open CategoryTheory CategoryTheory.Limits

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}
variable {X Y : PrismOver P R κ}

/-- 概要：平坦な被覆の有限広押し出しは site に存在する。
方針：同じ被覆の完備押し出しを反復する。
規約：BS 著者版 Corollary 3.12 の固定基底と濃度制限。
使われ方：増大付き Čech 余脈体の各項。 -/
theorem hasWidePushout_flat (hκ : IsAdmissibleCutoff P R κ)
    (f : X ⟶ Y) (hf : IsFaithfullyFlat f) (n : ℕ) :
    HasWidePushout X (fun _ : Fin n ↦ Y) (fun _ ↦ f) :=
  hasWidePushout_repeated f (fun {_} g ↦ by
    obtain ⟨_, _, _, h, _⟩ := exists_isPushout_isFaithfullyFlat hκ f hf g
    exact h.hasPushout) n

/-- 概要：平坦な被覆の site 上の増大付き Čech 余脈体。
方針：有限広押し出しの存在を用いて通常の余脈体を作る。
規約：BS 著者版 Corollary 3.12 (c) の完備 Čech 余脈体。
使われ方：構造環を適用して完備 Čech 複体を得る。 -/
@[expose] def flatAugmentedCechConerve (hκ : IsAdmissibleCutoff P R κ)
    (f : X ⟶ Y) (hf : IsFaithfullyFlat f) :
    CosimplicialObject.Augmented (PrismOver P R κ) :=
  @Arrow.augmentedCechConerve _ _ (Arrow.mk f) (fun n ↦ hasWidePushout_flat hκ f hf (n + 1))

end SerrePositivity.BhattScholze.Prismatic.PrismOver
