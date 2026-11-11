module
public import SerrePositivity.KST.SConstruction.AnodyneExtensionChoices
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # Kan 空間の二脚を貼る全選択空間
概要：同じ終点へ向かう二辺を保つ三角形の選択を可縮 Kan 空間にする。
方針：二脚を最後の二次ホーンへ貼り、anodyne 延長の厳密な fiber を使う。
規約：入力は写像空間でもよく、全パラメーターの単体を同時に保つ。
使われ方：coherent な因子の source→central←target を逆向きに貼る。
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

/-- 共通の終点を持つ二脚から作る、最後の二次ホーン上の射。 -/
def kanCospanHorn {K : SSet.{u}} {x y z : K _⦋0⦌}
    (a : K.Edge x z) (b : K.Edge y z) : (Λ[2, 2] : SSet.{u}) ⟶ K :=
  Classical.choose (horn₂₂.isPushout.exists_desc
    (SSet.yonedaEquiv.symm a.edge) (SSet.yonedaEquiv.symm b.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (a.tgt_eq.trans b.tgt_eq.symm)))

/-- ホーンの第一脚は入力した源から中央への辺。 -/
lemma kanCospanHorn_source {K : SSet.{u}} {x y z : K _⦋0⦌}
    (a : K.Edge x z) (b : K.Edge y z) :
    horn₂₂.ι₀₂ ≫ kanCospanHorn a b = SSet.yonedaEquiv.symm a.edge :=
  (Classical.choose_spec (horn₂₂.isPushout.exists_desc
    (SSet.yonedaEquiv.symm a.edge) (SSet.yonedaEquiv.symm b.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (a.tgt_eq.trans b.tgt_eq.symm)))).1

/-- ホーンの第二脚は入力した標的から中央への辺。 -/
lemma kanCospanHorn_target {K : SSet.{u}} {x y z : K _⦋0⦌}
    (a : K.Edge x z) (b : K.Edge y z) :
    horn₂₂.ι₁₂ ≫ kanCospanHorn a b = SSet.yonedaEquiv.symm b.edge :=
  (Classical.choose_spec (horn₂₂.isPushout.exists_desc
    (SSet.yonedaEquiv.symm a.edge) (SSet.yonedaEquiv.symm b.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (a.tgt_eq.trans b.tgt_eq.symm)))).2

/-- 二脚を厳密に固定する全三角形の単体的選択空間。 -/
def kanCospanPastingChoices {K : SSet.{u}} {x y z : K _⦋0⦌}
    (a : K.Edge x z) (b : K.Edge y z) : SSet.{u} :=
  anodyneExtensionChoices (horn 2 (2 : Fin 3)).ι (kanCospanHorn a b)

/-- 二脚の貼り合わせの全選択は可縮 Kan。標的自体の可縮性は不要。 -/
lemma kanCospanPastingChoices_isContractibleKan {K : SSet.{u}} [KanComplex K]
    {x y z : K _⦋0⦌} (a : K.Edge x z) (b : K.Edge y z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (kanCospanPastingChoices a b) :=
  anodyneExtensionChoices_isContractibleKan _ (anodyneExtensions.horn_ι (2 : Fin 3)) _

/-- 既存の任意の高次パラメーター部分を保って貼り合わせの選択を延ばせる。 -/
lemma kanCospanPastingChoices_relative_lifting {K : SSet.{u}} [KanComplex K]
    {x y z : K _⦋0⦌} (a : K.Edge x z) (b : K.Edge y z)
    {S T : SSet.{u}} (j : S ⟶ T) [CategoryTheory.Mono j]
    (q : S ⟶ kanCospanPastingChoices a b) :
    ∃ q' : T ⟶ kanCospanPastingChoices a b, j ≫ q' = q :=
  anodyneExtensionChoices_relative_lifting _ (anodyneExtensions.horn_ι (2 : Fin 3)) _ j q

/-- 選択した貼り合わせを実際の二単体の射へ戻す。 -/
def kanCospanPastingAt {K : SSet.{u}} {x y z : K _⦋0⦌}
    (a : K.Edge x z) (b : K.Edge y z) (v : (kanCospanPastingChoices a b) _⦋0⦌) :
    (Δ[2] : SSet.{u}) ⟶ K :=
  anodyneExtensionAt _ (kanCospanHorn a b) v

/-- 選択した二単体の 02 辺は元の第一脚を厳密に回収する。 -/
lemma kanCospanPastingAt_source {K : SSet.{u}} {x y z : K _⦋0⦌}
    (a : K.Edge x z) (b : K.Edge y z) (v : (kanCospanPastingChoices a b) _⦋0⦌) :
    stdSimplex.δ 1 ≫ kanCospanPastingAt a b v = SSet.yonedaEquiv.symm a.edge := by
  dsimp only [kanCospanPastingAt]
  rw [← horn.ι_ι_assoc (2 : Fin 3) 1 (by decide),
    anodyneExtensionAt_fac, kanCospanHorn_source]

/-- 選択した二単体の 12 辺は元の第二脚を厳密に回収する。 -/
lemma kanCospanPastingAt_target {K : SSet.{u}} {x y z : K _⦋0⦌}
    (a : K.Edge x z) (b : K.Edge y z) (v : (kanCospanPastingChoices a b) _⦋0⦌) :
    stdSimplex.δ 0 ≫ kanCospanPastingAt a b v = SSet.yonedaEquiv.symm b.edge := by
  dsimp only [kanCospanPastingAt]
  rw [← horn.ι_ι_assoc (2 : Fin 3) 0 (by decide),
    anodyneExtensionAt_fac, kanCospanHorn_target]

/-- 貼り合わせの二単体の 01 辺が源から標的への比較辺。 -/
def kanCospanPastedEdge {K : SSet.{u}} {x y z : K _⦋0⦌}
    (a : K.Edge x z) (b : K.Edge y z) (v : (kanCospanPastingChoices a b) _⦋0⦌) :
    K.Edge x y := by
  let t := SSet.yonedaEquiv (kanCospanPastingAt a b v)
  have h₁ : K.δ 1 t = a.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, kanCospanPastingAt_source]
    exact SSet.yonedaEquiv.apply_symm_apply _
  have h₀ : K.δ 0 t = b.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, kanCospanPastingAt_target]
    exact SSet.yonedaEquiv.apply_symm_apply _
  refine SSet.Edge.mk (K.δ 2 t) ?_ ?_
  · have ht : K.δ 1 (K.δ 2 t) = K.δ 1 (K.δ 1 t) :=
      K.δ_comp_δ_apply (i := (1 : Fin 2)) (j := 1) (by decide) t
    exact ht.trans ((congrArg (K.δ 1) h₁).trans a.src_eq)
  · have ht : K.δ 0 (K.δ 2 t) = K.δ 1 (K.δ 0 t) :=
      K.δ_comp_δ_apply (i := (0 : Fin 2)) (j := 1) (by decide) t
    exact ht.trans ((congrArg (K.δ 1) h₀).trans b.src_eq)

/-- 貼り合わせは元の二脚を両面に持つ実際の合成三角形。 -/
def kanCospanPastedTriangle {K : SSet.{u}} {x y z : K _⦋0⦌}
    (a : K.Edge x z) (b : K.Edge y z) (v : (kanCospanPastingChoices a b) _⦋0⦌) :
    SSet.Edge.CompStruct (kanCospanPastedEdge a b v) b a := by
  refine SSet.Edge.CompStruct.mk (SSet.yonedaEquiv (kanCospanPastingAt a b v)) rfl ?_ ?_
  · rw [← stdSimplex.yonedaEquiv_δ_comp, kanCospanPastingAt_target]
    exact SSet.yonedaEquiv.apply_symm_apply _
  · rw [← stdSimplex.yonedaEquiv_δ_comp, kanCospanPastingAt_source]
    exact SSet.yonedaEquiv.apply_symm_apply _

/-- 元の二脚と同じ一単体を持つ像の表示へ、選択した貼り合わせ三角形を移せる。 -/
lemma kanCospanPastedTriangle_map {K L : SSet.{u}} {x y z : K _⦋0⦌}
    (a : K.Edge x z) (b : K.Edge y z) (v : (kanCospanPastingChoices a b) _⦋0⦌)
    (H : K ⟶ L) {x' y' z' : L _⦋0⦌} (a' : L.Edge x' z') (b' : L.Edge y' z')
    (ha : (a.map H).edge = a'.edge) (hb : (b.map H).edge = b'.edge) :
    ∃ e : L.Edge x' y', Nonempty (SSet.Edge.CompStruct e b' a') ∧
      e.edge = ((kanCospanPastedEdge a b v).map H).edge := by
  have hx : H.app (Opposite.op ⦋0⦌) x = x' :=
    (a.map H).src_eq.symm.trans ((congrArg (L.δ 1) ha).trans a'.src_eq)
  have hy : H.app (Opposite.op ⦋0⦌) y = y' :=
    (b.map H).src_eq.symm.trans ((congrArg (L.δ 1) hb).trans b'.src_eq)
  let e := ((kanCospanPastedEdge a b v).map H).ofEq hx hy
  exact ⟨e, ⟨((kanCospanPastedTriangle a b v).map H).ofEq rfl hb ha⟩, rfl⟩

end SerrePositivity.KST.SConstruction
