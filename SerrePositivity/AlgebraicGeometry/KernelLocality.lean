module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
概要：Stacks 081T のスキーム論的稠密性に使う核の標的アフィン局所性。
方針：開基底変更の核の公式と切断環の同型の全射性を用いる。
規約：核の局所化に必要な準コンパクト性を明示する。
使われ方：blowup の中心外開包含の核が零であることを各チャートから検証する。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/--
概要：準コンパクト射の核は標的のアフィン開被覆上の引き戻しの零核から消える。
方針：核イデアルの開基底変更の公式を切断環同型で押し戻す。
規約：Stacks 081T、被約性を仮定せずスキーム論的な核を用いる。
使われ方：中心外開集合のスキーム論的稠密性。
-/
theorem ker_eq_bot_of_affineOpenCover_pullbacks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (𝒰 : Y.AffineOpenCover)
    (hf : ∀ i, (pullback.snd f (𝒰.f i)).ker = ⊥) : f.ker = ⊥ := by
  let V (i : 𝒰.I₀) : Y.affineOpens :=
    ⟨𝒰.f i ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion (𝒰.f i)⟩
  have hV : (⨆ i, (V i).1) = ⊤ := by
    simp only [V, Scheme.Hom.image_top_eq_opensRange]
    exact 𝒰.openCover.iSup_opensRange
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V hV
  intro i
  let W : (Spec (𝒰.X i)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have H := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f
    (pullback.snd f (𝒰.f i)) (pullback.fst f (𝒰.f i)) (𝒰.f i)
    (IsPullback.of_hasPullback f (𝒰.f i)).flip W
  rw [hf i] at H
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at H
  have HH := congrArg (Ideal.map ((𝒰.f i).appIso W).inv.hom) H
  rw [Ideal.map_bot, Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso W).inv).2] at HH
  exact HH.symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
