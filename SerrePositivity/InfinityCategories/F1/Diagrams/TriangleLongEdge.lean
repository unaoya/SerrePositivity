module

public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：二単体の長辺の包含の right anodyne 性。
方針：終点からの一次ホーンと最後の二次ホーンの貼り付けに分解する。
規約：長辺は面写像 δ₁ で表す。
使われ方：Kerodon Proposition 5.2.5.1、合成の三角形への相対 coslice の延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準区間への終点包含は right anodyne。
方針：任意の right fibration に対し指定終点から辺を持ち上げる。
規約：終点包含は δ₀ : Δ[0] → Δ[1]。
使われ方：Kerodon §4.2.4、Proposition 5.2.5.1 の長辺のセル分解。 -/
lemma endpointInclusion_rightAnodyne :
    rightAnodyneExtensions (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
  intro X Y q hq
  have : RightFibration q := ⟨hq⟩
  constructor
  intro a b sq
  let x := SSet.yonedaEquiv a
  have he : stdSimplex.δ 0 ≫ b =
      SSet.yonedaEquiv.symm (q.app (Opposite.op ⦋0⦌) x) := by
    rw [← SSet.yonedaEquiv_symm_comp]
    dsimp only [x]
    rw [Equiv.symm_apply_apply]
    exact sq.w.symm
  obtain ⟨f, hf, hfq, _⟩ := CartesianFibration.mem (p := q) |>.2 x b he
  exact CommSq.HasLift.mk' {
    l := f
    fac_left := hf.trans (SSet.yonedaEquiv.symm_apply_apply a)
    fac_right := hfq }

/-- 概要：二単体への長辺の包含は right anodyne。
方針：終点で辺を貼り付けた後、最後の二次ホーンを貼り付ける。
規約：長辺は δ₁、右 anodyne 性はモデル構造を使わない llp。
使われ方：Kerodon Proposition 5.2.5.1、長辺から三角形への錐の延長。 -/
lemma triangleLongEdge_rightAnodyne :
    rightAnodyneExtensions (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) := by
  have h₁ : rightAnodyneExtensions (horn₂₂.ι₀₂ : (Δ[1] : SSet.{u}) ⟶ Λ[2, 2]) :=
    MorphismProperty.of_isPushout horn₂₂.isPushout endpointInclusion_rightAnodyne
  have h₂ := rightAnodyneExtensions_horn (2 : Fin 3) (by decide)
  have h := rightAnodyneExtensions.comp_mem horn₂₂.ι₀₂ (horn 2 2).ι h₁ h₂
  rwa [horn.ι_ι] at h

/-- 概要：二単体の長辺の部分複体包含は right anodyne。
方針：長辺の標準単体による表示の同型を除く。
規約：部分複体は一番目の頂点を除いた面。
使われ方：Kerodon Proposition 5.2.5.1、相対 coslice の長辺への制限。 -/
lemma triangleLongFace_rightAnodyne :
    rightAnodyneExtensions (stdSimplex.face (n := 2) {(1 : Fin 3)}ᶜ :
      (Δ[2] : SSet.{u}).Subcomplex).ι := by
  rw [← rightAnodyneExtensions.cancel_left_of_respectsIso
    (stdSimplex.faceSingletonComplIso (1 : Fin 3)).hom]
  rw [stdSimplex.faceSingletonComplIso_hom_ι]
  exact triangleLongEdge_rightAnodyne

end SerrePositivity.InfinityCategories
