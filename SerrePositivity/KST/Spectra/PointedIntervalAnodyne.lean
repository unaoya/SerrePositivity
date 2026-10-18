module

public import SerrePositivity.KST.Spectra.PointedInterval

/-!
概要：基点つき区間の始点包含の anodyne 性。
方針：一次ホーンと零次標準単体の同型を用いる。
規約：モデル構造の存在を使わず Mathlib のホーン生成 anodyne 性を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.3。path space の全境界充填。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：一次ホーン Λ[1,0] は始点の面。
方針：残る面が一つであることを有限添字で検査する。
規約：面の添字は一、頂点の値は零。
使われ方：Kerodon §3.1.1、Goerss–Jardine I §7。始点包含の anodyne 性。 -/
theorem horn_one_zero_eq_face : (horn.{u} 1 0) = stdSimplex.face {(1 : Fin 2)}ᶜ := by
  rw [horn_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro j
    have hj0 : j.val ≠ 0 := j.property
    have hj1 : j.val = 1 := Fin.eq_one_of_ne_zero j.val hj0
    simpa only [hj1] using (le_refl (stdSimplex.face {(1 : Fin 2)}ᶜ : (Δ[1] : SSet.{u}).Subcomplex))
  · exact le_iSup_of_le ⟨1, by decide⟩ le_rfl

/-- 概要：区間の始点への零次面の包含は anodyne。
方針：一次ホーンと面の同定を面の標準同型で移す。
規約：射は Δ[0] から Δ[1] への δ₁。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.1。path space の充填。 -/
theorem interval_zeroFace_anodyne : anodyneExtensions (stdSimplex.δ.{u} (1 : Fin 2)) := by
  have hh : anodyneExtensions (stdSimplex.face.{u} {(1 : Fin 2)}ᶜ).ι := by
    rw [← horn_one_zero_eq_face]
    exact anodyneExtensions.horn_ι 0
  rw [← stdSimplex.faceSingletonComplIso_hom_ι (1 : Fin 2)]
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _) hh

/-- 概要：点つき区間の基点を与える射は anodyne。
方針：単位と Δ[0] の終対象としての同型を零次面の包含に前合成する。
規約：基点は始点の頂点零。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.3。path space の全境界充填。 -/
theorem pointedInterval_basepoint_anodyne : anodyneExtensions pointedInterval.{u}.hom := by
  let e : 𝟙_ SSet.{u} ≅ (Δ[0] : SSet.{u}) :=
    isTerminalTensorUnit.uniqueUpToIso stdSimplex.isTerminalObj₀
  have he : pointedInterval.{u}.hom = e.hom ≫ stdSimplex.δ (1 : Fin 2) := by
    ext m s
    apply stdSimplex.ext
    intro j
    rfl
  rw [he]
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _) interval_zeroFace_anodyne

end

end SerrePositivity.KST.Spectra
