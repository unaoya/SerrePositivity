module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：三角形の境界を、合成する二辺のホーンと対角辺の和として表示する。
方針：部分複体の和と交わりを計算し、格子の bicartesian square を pushout に移す。
規約：対角辺は δ₁、重なりは頂点 0 と 2 の和。
使われ方：二辺を固定し対角辺だけを動かす境界の path の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：三角形の対角辺と合成ホーンの重なり。
方針：二つの端頂点の部分複体の和を取る。
規約：中間頂点 1 は含めない。
使われ方：対角辺の path の端点を固定して貼る。 -/
def triangleDiagonalEndpoints : (Δ[2] : SSet.{u}).Subcomplex :=
  stdSimplex.face {0} ⊔ stdSimplex.face {2}

/-- 概要：合成ホーンと対角辺は、端点の上で貼り合わされて三角形の境界になる。
方針：ホーンの二面の和と、対角面との交わりを計算する。
規約：全て Δ[2] 内の部分複体として述べる。
使われ方：境界上の path の pushout による構成。 -/
lemma triangleBoundary_bicartSq : Subcomplex.BicartSq triangleDiagonalEndpoints
    (horn 2 1) (stdSimplex.face {0, 2}) (boundary 2 : (Δ[2] : SSet.{u}).Subcomplex) where
  sup_eq := by
    have hc₀ : ({0}ᶜ : Finset (Fin 3)) = {1, 2} := by decide
    have hc₁ : ({1}ᶜ : Finset (Fin 3)) = {0, 2} := by decide
    have hc₂ : ({2}ᶜ : Finset (Fin 3)) = {0, 1} := by decide
    apply le_antisymm
    · apply sup_le
      · rw [← horn₂₁.sq.sup_eq]
        apply sup_le
        · simpa only [hc₂] using (face_singleton_compl_le_boundary (2 : Fin 3))
        · simpa only [hc₀] using (face_singleton_compl_le_boundary (0 : Fin 3))
      · simpa only [hc₁] using (face_singleton_compl_le_boundary (1 : Fin 3))
    · rw [boundary_eq_iSup]
      apply iSup_le
      intro i
      fin_cases i
      · have h : stdSimplex.face {1, 2} ≤
            horn 2 1 ⊔ (stdSimplex.face {0, 2} : (Δ[2] : SSet.{u}).Subcomplex) :=
          le_sup_of_le_left (by rw [← horn₂₁.sq.sup_eq]; exact le_sup_right)
        change stdSimplex.face ({0}ᶜ : Finset (Fin 3)) ≤ _
        rw [hc₀]
        exact h
      · have h : stdSimplex.face {0, 2} ≤
            horn 2 1 ⊔ (stdSimplex.face {0, 2} : (Δ[2] : SSet.{u}).Subcomplex) := le_sup_right
        change stdSimplex.face ({1}ᶜ : Finset (Fin 3)) ≤ _
        rw [hc₁]
        exact h
      · have h : stdSimplex.face {0, 1} ≤
            horn 2 1 ⊔ (stdSimplex.face {0, 2} : (Δ[2] : SSet.{u}).Subcomplex) :=
          le_sup_of_le_left (by rw [← horn₂₁.sq.sup_eq]; exact le_sup_left)
        change stdSimplex.face ({2}ᶜ : Finset (Fin 3)) ≤ _
        rw [hc₂]
        exact h
  inf_eq := by
    rw [← horn₂₁.sq.sup_eq]
    calc
      _ = (stdSimplex.face {0, 1} ⊓ stdSimplex.face {0, 2}) ⊔
          (stdSimplex.face {1, 2} ⊓ stdSimplex.face {0, 2}) := by
        ext n x
        change ((x ∈ (stdSimplex.face {0, 1}).obj n ∨
          x ∈ (stdSimplex.face {1, 2}).obj n) ∧ x ∈ (stdSimplex.face {0, 2}).obj n) ↔
            (x ∈ (stdSimplex.face {0, 1}).obj n ∧ x ∈ (stdSimplex.face {0, 2}).obj n) ∨
              (x ∈ (stdSimplex.face {1, 2}).obj n ∧ x ∈ (stdSimplex.face {0, 2}).obj n)
        tauto
      _ = _ := by simp [stdSimplex.face_inter_face, triangleDiagonalEndpoints]

/-- 概要：端点・合成ホーン・対角辺・境界の包含は単体集合の pushout。
方針：部分複体の bicartesian square を単体集合へ移す。
規約：貼り合わせの両入力は重なり上で厳密に一致する。
使われ方：対角辺を動かす境界の path の descent。 -/
lemma triangleBoundary_isPushout :
    IsPushout (Subcomplex.homOfLE triangleBoundary_bicartSq.le₁₂)
      (Subcomplex.homOfLE triangleBoundary_bicartSq.le₁₃)
      (Subcomplex.homOfLE triangleBoundary_bicartSq.le₂₄)
      (Subcomplex.homOfLE triangleBoundary_bicartSq.le₃₄) :=
  triangleBoundary_bicartSq.isPushout

/-- 概要：対角辺の二端点は二つの頂点の空の重なり上の和。
方針：異なる頂点の部分複体の交わりは空。
規約：周囲は Δ[2]。
使われ方：重なり上の二射の等式を端点で検査する。 -/
lemma triangleDiagonalEndpoints_bicartSq : Subcomplex.BicartSq
    (⊥ : (Δ[2] : SSet.{u}).Subcomplex) (stdSimplex.face {0})
    (stdSimplex.face {2}) triangleDiagonalEndpoints where
  sup_eq := rfl
  inf_eq := by simp [stdSimplex.face_inter_face]

/-- 概要：対角辺の始点を重なりへ含める射。
方針：頂点の標準表示を和の左側へ含める。
規約：頂点は 0。
使われ方：対角辺の path の始点条件。 -/
noncomputable def triangleDiagonalEndpointZero : (Δ[0] : SSet.{u}) ⟶
    (triangleDiagonalEndpoints : SSet.{u}) :=
  (stdSimplex.faceSingletonIso (0 : Fin 3)).hom ≫ Subcomplex.homOfLE le_sup_left

/-- 概要：対角辺の終点を重なりへ含める射。
方針：頂点の標準表示を和の右側へ含める。
規約：頂点は 2。
使われ方：対角辺の path の終点条件。 -/
noncomputable def triangleDiagonalEndpointTwo : (Δ[0] : SSet.{u}) ⟶
    (triangleDiagonalEndpoints : SSet.{u}) :=
  (stdSimplex.faceSingletonIso (2 : Fin 3)).hom ≫ Subcomplex.homOfLE le_sup_right

/-- 概要：対角辺の重なり上の射は二端点で決まる。
方針：二つの頂点の pushout と零単体の標準同型を使う。
規約：標的は任意。
使われ方：境界の貼り合わせの一致条件。 -/
lemma triangleDiagonalEndpoints_hom_ext {Z : SSet.{u}}
    {f g : (triangleDiagonalEndpoints : SSet.{u}) ⟶ Z}
    (h₀ : triangleDiagonalEndpointZero ≫ f = triangleDiagonalEndpointZero ≫ g)
    (h₂ : triangleDiagonalEndpointTwo ≫ f = triangleDiagonalEndpointTwo ≫ g) : f = g := by
  apply triangleDiagonalEndpoints_bicartSq.isPushout.hom_ext
  · apply (cancel_epi (stdSimplex.faceSingletonIso (0 : Fin 3)).hom).mp
    exact h₀
  · apply (cancel_epi (stdSimplex.faceSingletonIso (2 : Fin 3)).hom).mp
    exact h₂

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
