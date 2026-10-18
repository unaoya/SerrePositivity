module

public import SerrePositivity.KST.Descent.AffineBaseChangeDescent
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# テンソル積モデルの実際の Cartesian 正方形

## 概要
分裂する底変換の降下に使ったテンソル積の二つの射影を、実際の引き戻しへ接続する。

## 方針
Mathlib の Spec とテンソル積の標準同型の二射影を保持して普遍性を移す。

## 規約
右因子への射影も元の Spec 作用と同変であることを検査する。
これだけで Čech の Tot や Fubini の証明が完了したとはしない。

## 使われ方
論文 補題 3.2 の τ 位相の層論を Čech 計算に置換する際の底変換の幾何。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace SerrePositivity.KST.Descent

variable (A B T : Type u) [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]

/-- 概要：テンソル積の指定二射影の実際の可換性（論文 補題 3.2）。
方針：標準同型の逆射と実際の引き戻しの二射影の公式を使う。
規約：左因子 B 上の係数射影を第一射影とする。
使われ方：Cartesian 正方形と、その同変性の検査。 -/
theorem tensorSpecSquare_comm :
    Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] T))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        T →ₐ[A] B ⊗[A] T).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A T)) := by
  have right : (pullbackSpecIso A B T).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        T →ₐ[A] B ⊗[A] T).toRingHom) := pullbackSpecIso_inv_snd A B T
  rw [← pullbackSpecIso_inv_fst' A B T, ← right]
  simp only [Category.assoc, pullback.condition]

/-- 概要：テンソル積の二射影は実際のスキームの引き戻し（論文 補題 3.2）。
方針：標準同型の二射影の公式で引き戻しの普遍性を移す。
規約：単なる対象の同型の存在でなく、指定された二射影の Cartesian 性。
使われ方：底変換した射の降下のテンソル積モデル。 -/
theorem tensorSpecSquare_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] T))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        T →ₐ[A] B ⊗[A] T).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A T))) :=
  IsPullback.of_iso_pullback ⟨tensorSpecSquare_comm A B T⟩ (pullbackSpecIso A B T).symm
    (pullbackSpecIso_inv_fst' A B T) (pullbackSpecIso_inv_snd A B T)

variable {A B T} {G : Type u} [Group G] [MulSemiringAction G T] [SMulCommClass G A T]

/-- 概要：右因子への Spec の射影は指定された群作用と同変（論文 補題 3.2）。
方針：Spec の反変性を使い、右因子上の環準同型の等式を検査する。
規約：両側の Spec の左作用は逆元による comap。
使われ方：Cartesian 正方形の同変比較と Čech 底変換。 -/
theorem tensorSpecSquare_right_equivariant (g : G) :
    (specAction (T := B ⊗[A] T) g).asIso.hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          T →ₐ[A] B ⊗[A] T).toRingHom) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          T →ₐ[A] B ⊗[A] T).toRingHom) ≫ (specAction (T := T) g).asIso.hom := by
  change Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G (B ⊗[A] T) g⁻¹)) ≫ _ =
    _ ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G T g⁻¹))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

end SerrePositivity.KST.Descent
