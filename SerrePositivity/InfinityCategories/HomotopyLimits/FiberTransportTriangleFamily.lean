module

public import SerrePositivity.InfinityCategories.F1.FiberTransportFamily
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningCompositionLift

/-!
概要：元の三角形の全パラメータ族に沿う fiber 輸送の合成。
方針：二辺の元の prism を同じパラメータで貼り、長辺の輸送族を構成する。
規約：点ごとの合成比較を自然な族とは仮定せず、一つの三角形 prism を充填する。
使われ方：元の区間 Hom の前合成族と Yoneda の恒等点評価の両立。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {E B K : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b c : B _⦋0⦌}
  (T : (Δ[2] : SSet.{u}) ⊗ K ⟶ B)
  (U : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a))
    ((stdSimplex.δ (2 : Fin 3) ▷ K) ≫ T))
  (V : FiberTransportFamily (b := c) p (𝟙 (vertexFiber p b))
    ((stdSimplex.δ (0 : Fin 3) ▷ K) ≫ T))

/-- 元の二つの輸送 prism の同じパラメータでの合成を、元の長辺の輸送族として保持する。 -/
def fiberTransportFamilyTriangleComposite :
    FiberTransportFamily (b := c) p (𝟙 (vertexFiber p a))
      ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ T) := by
  let A := vertexFiber p a
  let j := lift U.endpoint (snd A K)
  let W := (Δ[1] ◁ j) ≫ V.prism
  let t := (Δ[2] ◁ snd A K) ≫ T
  have hw : prismEndpoint 1 (A ⊗ K) ≫ U.prism = prismEndpoint 0 (A ⊗ K) ≫ W := by
    dsimp only [W]
    rw [U.finish, ← Category.assoc, prismEndpoint_naturality, Category.assoc, V.start]
    simp only [Category.id_comp, ← Category.assoc, j, lift_fst]
  have hp₀₁ : U.prism ≫ p = (stdSimplex.δ (2 : Fin 3) ▷ (A ⊗ K)) ≫ t := by
    rw [U.over_base]
    exact (trianglePrism_restrict_baseChange (snd A K) T (2 : Fin 3)).symm
  have hp₁₂ : W ≫ p = (stdSimplex.δ (0 : Fin 3) ▷ (A ⊗ K)) ≫ t := by
    dsimp only [W]
    rw [Category.assoc, V.over_base, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
    have hj : j ≫ snd (vertexFiber p b) K = snd A K := lift_snd _ _
    rw [hj]
    exact (trianglePrism_restrict_baseChange (snd A K) T (0 : Fin 3)).symm
  let h := innerFibration_fillTrianglePrism p U.prism W t hw hp₀₁ hp₁₂
  let S := h.choose
  have hS₀₁ := h.choose_spec.1
  have hS₁₂ := h.choose_spec.2.1
  have hSp := h.choose_spec.2.2
  let H := (stdSimplex.δ (1 : Fin 3) ▷ (A ⊗ K)) ≫ S
  have hz : prismEndpoint 0 (A ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (A ⊗ K)) =
      prismEndpoint 0 (A ⊗ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ (A ⊗ K)) := rfl
  have ho : prismEndpoint 1 (A ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (A ⊗ K)) =
      prismEndpoint 1 (A ⊗ K) ≫ (stdSimplex.δ (0 : Fin 3) ▷ (A ⊗ K)) := rfl
  refine ⟨j ≫ V.endpoint, H, ?_, ?_, ?_⟩
  · dsimp only [H]
    rw [← Category.assoc, hz, Category.assoc, hS₀₁]
    exact U.start
  · dsimp only [H]
    rw [← Category.assoc, ho, Category.assoc, hS₁₂]
    dsimp only [W]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, V.finish, Category.assoc]
  · dsimp only [H]
    rw [Category.assoc, hSp]
    exact trianglePrism_restrict_baseChange (snd A K) T (1 : Fin 3)

/-- 合成した元の輸送族の写像は、同じパラメータでの二つの全 fiber Hom 作用の合成。 -/
lemma fiberTransportFamilyTriangleComposite_map :
    (fiberTransportFamilyTriangleComposite p T U V).map =
      lift U.map V.map ≫ MonoidalClosed.comp (vertexFiber p a) (vertexFiber p b)
        (vertexFiber p c) := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro k
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  change V.endpoint.app d (U.endpoint.app d (x, K.map α k), K.map α k) =
    V.endpoint.app d
      (U.endpoint.app d (x, K.map (α ≫ 𝟙 d) k), K.map (α ≫ 𝟙 d) k)
  simp only [Category.comp_id]

/-- 元の長辺の輸送族と二辺の合成を、全パラメータ上の一つの関手同型で結ぶ。 -/
def fiberTransportFamilyTriangle_mapIso
    (W : FiberTransportFamily (b := c) p (𝟙 (vertexFiber p a))
      ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ T))
    (hc : prismEndpoint 1 K ≫ ((stdSimplex.δ (1 : Fin 3) ▷ K) ≫ T) = SSet.const c) :
    FunctorIso W.map (lift U.map V.map ≫
      MonoidalClosed.comp (vertexFiber p a) (vertexFiber p b) (vertexFiber p c)) := by
  have h := W.mapIso p (𝟙 _) _ hc (fiberTransportFamilyTriangleComposite p T U V)
  rw [fiberTransportFamilyTriangleComposite_map] at h
  exact h

end SerrePositivity.InfinityCategories.HomotopyLimits
