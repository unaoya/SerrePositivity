module
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-! # 全指定面の整合族からの実境界写像

概要：二次以上の標準境界を、全余次元一面と共有余次元二面の多重余等化子で貼る。
方針：既存の部分複体の多重余等化子と、面の同型による制限公式を使う。
規約：標的は任意の単体集合。使われ方：有限次数錐から次次数の実境界写像を作る。

対応節は Kerodon 1.1（Tag 0004）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

/-- 標準境界を全余次元一面と全共有面で表す多重余等化子図式。 -/
lemma boundaryFaceMulticoequalizer (n : ℕ) :
    Subcomplex.MulticoequalizerDiagram (boundary (n + 2) : (Δ[n + 2] : SSet.{u}).Subcomplex)
      (fun j : Fin (n + 3) => stdSimplex.face {j}ᶜ)
      (fun j k => stdSimplex.face {j, k}ᶜ) where
  iSup_eq := (boundary_eq_iSup (n + 2)).symm
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

/-- 標準境界は、全指定面の同じ多重余等化子である。 -/
def boundaryFaceIsColimit (n : ℕ) :
    IsColimit ((boundaryFaceMulticoequalizer.{u} n).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  (boundaryFaceMulticoequalizer n).isColimit'

/-- 全指定面が全ての共有面上で一致する条件。 -/
def BoundaryFaceCompatible {n : ℕ} {X : SSet.{u}} (f : Fin (n + 3) → (Δ[n + 1] ⟶ X)) : Prop :=
  ∀ j k (hjk : j < k),
    stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k

/-- 全指定面の整合性を、多重余等化子の余錐へ渡す。 -/
def boundaryFaceCocone {n : ℕ} {X : SSet.{u}} {f : Fin (n + 3) → (Δ[n + 1] ⟶ X)}
    (hf : BoundaryFaceCompatible f) :
    Multicofork ((boundaryFaceMulticoequalizer n).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun j => (stdSimplex.faceSingletonComplIso j).inv ≫ f j) (by
    rintro ⟨⟨a, b⟩, hab : a < b⟩
    dsimp [boundaryFaceMulticoequalizer]
    rw [stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred_assoc _ _ hab,
      stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred_assoc _ _ hab,
      hf a b hab])

/-- 全指定面の整合族から貼り合わせる、実際の全境界写像。 -/
def boundaryFaceGluing {n : ℕ} {X : SSet.{u}} {f : Fin (n + 3) → (Δ[n + 1] ⟶ X)}
    (hf : BoundaryFaceCompatible f) : (∂Δ[n + 2] : SSet.{u}) ⟶ X :=
  (boundaryFaceIsColimit n).desc (boundaryFaceCocone hf)

/-- 貼った実境界写像は、元の全指定面を厳密に保つ。 -/
lemma boundaryFaceGluing_face {n : ℕ} {X : SSet.{u}} {f : Fin (n + 3) → (Δ[n + 1] ⟶ X)}
    (hf : BoundaryFaceCompatible f) (j : Fin (n + 3)) :
    boundary.ι j ≫ boundaryFaceGluing hf = f j := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso j).inv,
    boundary.faceSingletonComplIso_inv_ι_assoc]
  have he := (boundaryFaceIsColimit n).fac (boundaryFaceCocone hf) (.right j)
  exact he

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
