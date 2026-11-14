module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDP
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# 多項式の pd Čech 模型

## 概要
第 0 頂点の通常の座標と、それ以外の頂点との差の自由 pd 代数で各項を表す。

## 方針
頂点写像を差の加群に線形に延長し、自由 pd 代数の関手性を使う。

## 規約
第 0 頂点との差は零とする。

## 使われ方
結晶比較の余分な δ 座標の収縮と pd de Rham 比較。
-/

public noncomputable section

open CategoryTheory Algebra.TensorProduct
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (k : Type u) [CommRing k] (r : ℕ)

/-- 第 0 頂点の座標と残りの頂点との差の自由 pd 代数。 -/
abbrev pdRaw (n : ℕ) :=
  MvPolynomial (Fin r) k ⊗[k] DividedPowerAlgebra k ((Fin r × Fin n) →₀ k)

private abbrev Diff (n : SimplexCategory) := (Fin r × Fin n.len) →₀ k

private def vertexDiff (n : SimplexCategory) (j : Fin r) (i : Fin (n.len + 1)) : Diff k r n :=
  Fin.cases 0 (fun a => Finsupp.single (j, a) 1) i

private def diffMap {m n : SimplexCategory} (θ : m ⟶ n) : Diff k r m →ₗ[k] Diff k r n :=
  Finsupp.linearCombination k fun a =>
    vertexDiff k r n a.1 (θ.toOrderHom a.2.succ) -
      vertexDiff k r n a.1 (θ.toOrderHom 0)

private theorem diffMap_vertex {m n : SimplexCategory} (θ : m ⟶ n)
    (j : Fin r) (i : Fin (m.len + 1)) :
    diffMap k r θ (vertexDiff k r m j i) =
      vertexDiff k r n j (θ.toOrderHom i) - vertexDiff k r n j (θ.toOrderHom 0) := by
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [vertexDiff]
  · simp [vertexDiff, diffMap, Finsupp.linearCombination_single]

private theorem diffMap_id (n : SimplexCategory) : diffMap k r (𝟙 n) = LinearMap.id := by
  apply (Finsupp.basisSingleOne (R := k)).ext
  intro a
  obtain ⟨j,i⟩ := a
  simpa [vertexDiff] using diffMap_vertex k r (𝟙 n) j i.succ

private theorem diffMap_comp {m n l : SimplexCategory} (θ : m ⟶ n) (ψ : n ⟶ l) :
    diffMap k r (θ ≫ ψ) = (diffMap k r ψ).comp (diffMap k r θ) := by
  apply (Finsupp.basisSingleOne (R := k)).ext
  rintro ⟨j,i⟩
  change diffMap k r (θ ≫ ψ) (vertexDiff k r m j i.succ) =
    diffMap k r ψ (diffMap k r θ (vertexDiff k r m j i.succ))
  rw [diffMap_vertex, diffMap_vertex, map_sub, diffMap_vertex, diffMap_vertex,
    sub_sub_sub_cancel_right]
  rfl

private def pdDiff (n : SimplexCategory) : Diff k r n →ₗ[k] pdRaw k r n.len :=
  (includeRight : DividedPowerAlgebra k (Diff k r n) →ₐ[k] _).toLinearMap.comp
    (DividedPowerAlgebra.embed k (Diff k r n))

private def baseVar (n : SimplexCategory) (j : Fin r) : pdRaw k r n.len :=
  (includeLeft : MvPolynomial (Fin r) k →ₐ[k] _) (MvPolynomial.X j)

private def copy (n : SimplexCategory) (j : Fin r) (i : Fin (n.len + 1)) : pdRaw k r n.len :=
  baseVar k r n j + pdDiff k r n (vertexDiff k r n j i)

private def pdRawMap {m n : SimplexCategory} (θ : m ⟶ n) : pdRaw k r m.len →ₐ[k] pdRaw k r n.len :=
  Algebra.TensorProduct.lift
    (MvPolynomial.aeval fun j => copy k r n j (θ.toOrderHom 0))
    (includeRight.comp (DividedPowerAlgebra.map k (diffMap k r θ))) (fun _ _ => Commute.all _ _)

private theorem pdRawMap_left {m n : SimplexCategory} (θ : m ⟶ n) :
    (pdRawMap k r θ).comp includeLeft = MvPolynomial.aeval (fun j => copy k r n j (θ.toOrderHom 0)) :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

private theorem pdRawMap_right {m n : SimplexCategory} (θ : m ⟶ n) :
    (pdRawMap k r θ).comp includeRight = includeRight.comp (DividedPowerAlgebra.map k (diffMap k r θ)) :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

private theorem pdRawMap_baseVar {m n : SimplexCategory} (θ : m ⟶ n) (j : Fin r) :
    pdRawMap k r θ (baseVar k r m j) = copy k r n j (θ.toOrderHom 0) := by
  have h := DFunLike.congr_fun (pdRawMap_left k r θ) (MvPolynomial.X j)
  exact h.trans (MvPolynomial.aeval_X _ _)

private theorem pdRawMap_pdDiff {m n : SimplexCategory} (θ : m ⟶ n) (x : Diff k r m) :
    pdRawMap k r θ (pdDiff k r m x) = pdDiff k r n (diffMap k r θ x) := by
  have h := DFunLike.congr_fun (pdRawMap_right k r θ) (DividedPowerAlgebra.embed k _ x)
  exact h.trans (congrArg includeRight (DividedPowerAlgebra.map_embed_apply k (diffMap k r θ)))

private theorem pdRawMap_copy {m n : SimplexCategory} (θ : m ⟶ n)
    (j : Fin r) (i : Fin (m.len + 1)) :
    pdRawMap k r θ (copy k r m j i) = copy k r n j (θ.toOrderHom i) := by
  simp only [copy, map_add, pdRawMap_baseVar, pdRawMap_pdDiff, diffMap_vertex, map_sub]
  abel

private theorem pdRawMap_id (n : SimplexCategory) : pdRawMap k r (𝟙 n) = AlgHom.id k _ := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro j
    change pdRawMap k r (𝟙 n) (baseVar k r n j) = baseVar k r n j
    rw [pdRawMap_baseVar]
    simp [copy, vertexDiff]
  · change (pdRawMap k r (𝟙 n)).comp includeRight = includeRight
    rw [pdRawMap_right, diffMap_id, DividedPowerAlgebra.map_id]
    rfl

private theorem pdRawMap_comp {m n l : SimplexCategory} (θ : m ⟶ n) (ψ : n ⟶ l) :
    pdRawMap k r (θ ≫ ψ) = (pdRawMap k r ψ).comp (pdRawMap k r θ) := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro j
    change pdRawMap k r (θ ≫ ψ) (baseVar k r m j) =
      pdRawMap k r ψ (pdRawMap k r θ (baseVar k r m j))
    rw [pdRawMap_baseVar, pdRawMap_baseVar, pdRawMap_copy]
    rfl
  · change (pdRawMap k r (θ ≫ ψ)).comp includeRight =
      ((pdRawMap k r ψ).comp (pdRawMap k r θ)).comp includeRight
    rw [pdRawMap_right]
    rw [AlgHom.comp_assoc, pdRawMap_right, ← AlgHom.comp_assoc, pdRawMap_right,
      AlgHom.comp_assoc, diffMap_comp, DividedPowerAlgebra.map_comp]

/-- 余面と余退化は各頂点の座標を添字写像で送る未完備 pd Čech 模型。 -/
def pdRawModel : SerrePositivity.Cosimplicial.CosimplicialAlgebra k where
  obj n := Under.mk (CommRingCat.ofHom (algebraMap k (pdRaw k r n.len)))
  map θ := Under.homMk (CommRingCat.ofHom (pdRawMap k r θ).toRingHom) (by
    apply CommRingCat.hom_ext
    exact RingHom.ext (pdRawMap k r θ).commutes)
  map_id n := by
    apply Under.UnderMorphism.ext
    exact congrArg (fun f => CommRingCat.ofHom (AlgHom.toRingHom f)) (pdRawMap_id k r n)
  map_comp θ ψ := by
    apply Under.UnderMorphism.ext
    exact congrArg (fun f => CommRingCat.ofHom (AlgHom.toRingHom f)) (pdRawMap_comp k r θ ψ)

end SerrePositivity.BhattScholze.Prismatic
