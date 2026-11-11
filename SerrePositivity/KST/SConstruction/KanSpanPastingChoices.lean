module
public import SerrePositivity.KST.SConstruction.AnodyneExtensionChoices
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # 共通始点の二辺を保つ全貼り合わせ空間
概要：元の二つの三角形の復号を外側ホーンへ貼り、全合成三角形を可縮 Kan 空間にする。
方針：二脚の始点を厳密に照合し、同じホーンの anodyne 延長の fiber を取る。
規約：指定する二脚を変更せず、パラメータ境界の既存の全三角形を保持する。
使われ方：元の K square の二つの三角形を共通パラメータへ貼る際の選択の制御。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 同じ元の始点を持つ二脚を、共通の外側ホーンの全次数に貼る。 -/
def kanSpanHorn {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) : (Λ[2, 0] : SSet.{u}) ⟶ K :=
  Classical.choose (horn₂₀.isPushout.exists_desc
    (SSet.yonedaEquiv.symm a.edge) (SSet.yonedaEquiv.symm b.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (a.src_eq.trans b.src_eq.symm)))

/-- 第一脚を同じホーンへの制限で厳密に回収する。 -/
lemma kanSpanHorn_source {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) :
    horn₂₀.ι₀₁ ≫ kanSpanHorn a b = SSet.yonedaEquiv.symm a.edge :=
  (Classical.choose_spec (horn₂₀.isPushout.exists_desc
    (SSet.yonedaEquiv.symm a.edge) (SSet.yonedaEquiv.symm b.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (a.src_eq.trans b.src_eq.symm)))).1

/-- 第二脚を同じホーンへの制限で厳密に回収する。 -/
lemma kanSpanHorn_target {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) :
    horn₂₀.ι₀₂ ≫ kanSpanHorn a b = SSet.yonedaEquiv.symm b.edge :=
  (Classical.choose_spec (horn₂₀.isPushout.exists_desc
    (SSet.yonedaEquiv.symm a.edge) (SSet.yonedaEquiv.symm b.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (a.src_eq.trans b.src_eq.symm)))).2

/-- 二つの元の脚を厳密に固定する、全三角形の単体的選択空間。 -/
def kanSpanPastingChoices {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) : SSet.{u} :=
  anodyneExtensionChoices (horn 2 (0 : Fin 3)).ι (kanSpanHorn a b)

/-- Kan 標的では全三角形の選択は可縮 Kan。 -/
lemma kanSpanPastingChoices_isContractibleKan {K : SSet.{u}} [KanComplex K]
    {z x y : K _⦋0⦌} (a : K.Edge z x) (b : K.Edge z y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (kanSpanPastingChoices a b) :=
  anodyneExtensionChoices_isContractibleKan _ (anodyneExtensions.horn_ι (0 : Fin 3)) _

/-- 既存の任意の高次パラメータ部分を厳密に保って貼り合わせの選択を延ばす。 -/
lemma kanSpanPastingChoices_relative_lifting {K : SSet.{u}} [KanComplex K]
    {z x y : K _⦋0⦌} (a : K.Edge z x) (b : K.Edge z y)
    {T U : SSet.{u}} (j : T ⟶ U) [Mono j] (q : T ⟶ kanSpanPastingChoices a b) :
    ∃ q' : U ⟶ kanSpanPastingChoices a b, j ≫ q' = q :=
  anodyneExtensionChoices_relative_lifting _ (anodyneExtensions.horn_ι (0 : Fin 3)) _ j q

/-- 選択の頂点から、元の二辺を両面に持つ実際の二単体の射を取り出す。 -/
def kanSpanPastingAt {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) (v : (kanSpanPastingChoices a b) _⦋0⦌) :
    (Δ[2] : SSet.{u}) ⟶ K :=
  anodyneExtensionAt _ (kanSpanHorn a b) v

/-- 元の第一脚を実二単体の 01 辺として回収する。 -/
lemma kanSpanPastingAt_source {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) (v : (kanSpanPastingChoices a b) _⦋0⦌) :
    stdSimplex.δ 2 ≫ kanSpanPastingAt a b v = SSet.yonedaEquiv.symm a.edge := by
  dsimp only [kanSpanPastingAt]
  rw [← horn.ι_ι_assoc (0 : Fin 3) 2 (by decide),
    anodyneExtensionAt_fac, kanSpanHorn_source]

/-- 元の第二脚を実二単体の 02 辺として回収する。 -/
lemma kanSpanPastingAt_target {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) (v : (kanSpanPastingChoices a b) _⦋0⦌) :
    stdSimplex.δ 1 ≫ kanSpanPastingAt a b v = SSet.yonedaEquiv.symm b.edge := by
  dsimp only [kanSpanPastingAt]
  rw [← horn.ι_ι_assoc (0 : Fin 3) 1 (by decide),
    anodyneExtensionAt_fac, kanSpanHorn_target]

/-- 同じ貼り合わせの欠けていた 12 辺を、元の二脚の終点の間の実辺として得る。 -/
def kanSpanPastedEdge {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) (v : (kanSpanPastingChoices a b) _⦋0⦌) :
    K.Edge x y := by
  let t := SSet.yonedaEquiv (kanSpanPastingAt a b v)
  have h₂ : K.δ 2 t = a.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, kanSpanPastingAt_source]
    exact SSet.yonedaEquiv.apply_symm_apply _
  have h₁ : K.δ 1 t = b.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, kanSpanPastingAt_target]
    exact SSet.yonedaEquiv.apply_symm_apply _
  refine SSet.Edge.mk (K.δ 0 t) ?_ ?_
  · have ht : K.δ 1 (K.δ 0 t) = K.δ 0 (K.δ 2 t) :=
      (K.δ_comp_δ_apply (i := (0 : Fin 2)) (j := 1) (by decide) t).symm
    exact ht.trans ((congrArg (K.δ 0) h₂).trans a.tgt_eq)
  · have ht : K.δ 0 (K.δ 0 t) = K.δ 0 (K.δ 1 t) :=
      (K.δ_comp_δ_apply (i := (0 : Fin 2)) (j := 0) (by decide) t).symm
    exact ht.trans ((congrArg (K.δ 0) h₁).trans b.tgt_eq)

/-- 元の二脚と同じ実二単体を保持する、三辺を指定した合成三角形。 -/
def kanSpanPastedTriangle {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) (v : (kanSpanPastingChoices a b) _⦋0⦌) :
    SSet.Edge.CompStruct a (kanSpanPastedEdge a b v) b := by
  refine SSet.Edge.CompStruct.mk (SSet.yonedaEquiv (kanSpanPastingAt a b v)) ?_ rfl ?_
  · rw [← stdSimplex.yonedaEquiv_δ_comp, kanSpanPastingAt_source]
    exact SSet.yonedaEquiv.apply_symm_apply _
  · rw [← stdSimplex.yonedaEquiv_δ_comp, kanSpanPastingAt_target]
    exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.KST.SConstruction
