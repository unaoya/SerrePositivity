module

public import SerrePositivity.AlgebraicGeometry.BlowupFunctor

/-!
概要：KST §5 の基礎環同型によるアフィン blowup の移送。
方針：中心を保つ両方向の比較射を作り、合成則で逆性を確認する。
規約：中心は像イデアルとの等式で同定する。
使われ方：アフィン開集合の切断環と Spec の大域切断の自然同型の比較。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

/--
概要：中心を保つ環同型の逆も中心を保つ。
方針：イデアルの像の合成則と環同型の逆性を使う。
規約：KST §5、中心の同定を明示的な等式として与える。
使われ方：blowup 比較射の逆射の構成。
-/
theorem center_map_ringEquiv_symm (e : R ≃+* S) (hJ : I.map e.toRingHom = J) :
    J.map e.symm.toRingHom = I := by
  rw [← hJ, Ideal.map_map]
  have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
    ext x
    exact e.symm_apply_apply x
  rw [hcomp, Ideal.map_id]

set_option backward.isDefEq.respectTransparency false in
/--
概要：中心を保つ基礎環同型はアフィン blowup の実際のスキーム同型を誘導する。
方針：順逆の中心比較射を合成し、恒等射公式を使う。
規約：KST §5、同型は標的環の blowup から元の環の blowup へ向かう。
使われ方：切断環の自然同型を介したアフィン開集合の貼り合わせ。
-/
def affineBlowupRingEquivIso (e : R ≃+* S) (hJ : I.map e.toRingHom = J) :
    affineBlowup J ≅ affineBlowup I := by
  let hI := center_map_ringEquiv_symm I J e hJ
  refine { hom := affineBlowupCenterMap I J e.toRingHom hJ
           inv := affineBlowupCenterMap J I e.symm.toRingHom hI
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · rw [affineBlowupCenterMap_comp]
    have hcomp : e.toRingHom.comp e.symm.toRingHom = RingHom.id S := by
      ext x
      exact e.apply_symm_apply x
    simpa only [hcomp] using affineBlowupCenterMap_id J
  · rw [affineBlowupCenterMap_comp]
    have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
      ext x
      exact e.symm_apply_apply x
    simpa only [hcomp] using affineBlowupCenterMap_id I

/--
概要：環同型による blowup の同型は基底の Spec の同型と両立する。
方針：中心比較射の基底両立性を使う。
規約：KST §5、元の基底環への構造射を明示する。
使われ方：一般スキームの構造射をアフィン開集合上で貼り合わせる。
-/
@[reassoc] theorem affineBlowupRingEquivIso_hom_base (e : R ≃+* S)
    (hJ : I.map e.toRingHom = J) :
    (affineBlowupRingEquivIso I J e hJ).hom ≫ affineBlowupπ I =
      affineBlowupπ J ≫ Spec.map (CommRingCat.ofHom e.toRingHom) :=
  affineBlowupCenterMap_base I J e.toRingHom hJ

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
