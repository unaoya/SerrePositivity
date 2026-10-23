module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedPrismEquivalenceSource
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderGeneralComparison

/-!
概要：区間上の left fibration を fiber 間の輸送の写像円柱で比較する。
方針：実際の輸送 prism の両端の同一視と全辺の cocartesian 性を使う。
規約：円柱から元の全空間への比較を前合成同値として証明する。
使われ方：Kerodon Lemma 5.6.9.1 の表現空間と中間空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：区間上の left fibration の輸送写像円柱から全空間への実際の比較は前合成同値。
方針：両 fiber の比較を恒等射とし、全垂直辺の cocartesian 性を使う。
規約：輸送 f と prism H は任意の選択でよい。
使われ方：写像円柱への制限による表現空間の比較。 -/
lemma intervalTransportCylinder_isPrecompositionEquivalence {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [LeftFibration p]
    (f : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (H : Δ[1] ⊗ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h₁ : prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hp : H ≫ p = fst Δ[1] _) :
    IsPrecompositionEquivalence
      (pushout.desc H (vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h₁) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  apply mappingCylinder_isPrecompositionEquivalence f p H _ h₁ hp (vertexFiberι_comp _ _)
    (𝟙 _) (by simpa using h₀.symm) (𝟙 _) (Category.id_comp _)
    (isPrecompositionEquivalence_id _) (isPrecompositionEquivalence_id _)
  intro x
  exact isCocartesianEdge_of_leftFibration p _

/-- 概要：区間上の任意の left fibration は輸送の写像円柱からの前合成同値を持つ。
方針：始点 fiber の包含を普遍区間に沿って持ち上げ、終点から輸送を定義する。
規約：全空間の小ささ以外の追加の存在仮定は要求しない。
使われ方：境界を保つ表現の延長を写像円柱上の問題へ移す。 -/
lemma exists_intervalTransportCylinder_comparison {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [LeftFibration p] :
    ∃ (f : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
        vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (H : Δ[1] ⊗ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
      (h₁ : prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))),
      prismEndpoint 0 _ ≫ H = vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ∧
      H ≫ p = fst Δ[1] _ ∧ IsPrecompositionEquivalence
        (pushout.desc H (vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h₁) := by
  obtain ⟨H, H₀, Hp⟩ := leftFibration_lift_prism p
    (vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (fst Δ[1] _) (by
      rw [vertexFiberι_comp]
      rfl)
  have H₁ : (prismEndpoint 1 _ ≫ H) ≫ p =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    rw [Category.assoc, Hp]
    rfl
  let f := vertexFiberLift p _ (prismEndpoint 1 _ ≫ H) H₁
  have h₁ : prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι p _ := rfl
  exact ⟨f, H, h₁, H₀, Hp, intervalTransportCylinder_isPrecompositionEquivalence p f H H₀ h₁ Hp⟩

end SerrePositivity.InfinityCategories
