module

public import SerrePositivity.InfinityCategories.Core.BoundaryPrismOpposite
public import SerrePositivity.InfinityCategories.Core.CocartesianPrismBoundary

/-!
概要：可逆な最後の垂直辺を持つ prism の終点を固定した相対延長。
方針：標準単体と境界の prism を反転し、先頭側の相対充填を適用して戻す。
規約：元・基底は quasicategory、射は inner fibration。
使われ方：Kerodon §7.1.5 の fiber 内の充填から元の境界への復帰。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：境界の最後の頂点上の垂直辺。
方針：区間の恒等一単体と境界の最後の頂点の定値一単体を組にする。
規約：境界の次元は n+1。
使われ方：Kerodon §7.1.5 の終点側の外側ホーンの可逆な辺。 -/
def prismBoundaryLastVerticalEdge (n : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u})) _⦋1⦌ :=
  ⟨SSet.yonedaEquiv (𝟙 Δ[1]),
    PinchedHom.constant (X := (boundary (n + 1) : SSet.{u}))
      ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), vertex_mem_boundary n (Fin.last (n + 1))⟩ 1⟩

/-- 概要：境界の最後の垂直辺が可逆なら反転後の最初の垂直辺も可逆。
方針：二つの辺の一次単体を反転した辺として同定する。
規約：標的の quasicategory 性だけを仮定する。
使われ方：Kerodon §7.1.5 の相対 prism の終点側の充填。 -/
lemma reverseBoundaryPrism_first_isInvertible {E : SSet.{u}} [Quasicategory E] (n : ℕ)
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u}) ⟶ E)
    (hH : IsInvertibleEdge (edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (prismBoundaryLastVerticalEdge n)))) :
    IsInvertibleEdge (edgeOfSimplex ((reverseBoundaryPrism H).app (Opposite.op ⦋1⦌)
      (prismBoundaryFirstVerticalEdge n))) := by
  have h := IsInvertibleEdge.op hH
  have he : (edgeOp (edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (prismBoundaryLastVerticalEdge n)))).edge =
      (edgeOfSimplex ((reverseBoundaryPrism H).app (Opposite.op ⦋1⦌)
        (prismBoundaryFirstVerticalEdge n))).edge := by
    change SSet.opObjEquiv.symm (H.app (Opposite.op ⦋1⦌) (_, _)) =
      SSet.opObjEquiv.symm (H.app (Opposite.op ⦋1⦌) (_, _))
    congr 2
    apply Prod.ext
    · apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    · apply Subtype.ext
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      change (Fin.last (n + 1)).val = ((0 : Fin (n + 2)).rev).val
      simp
  exact (isInvertibleEdge_congr he).mp h

/-- 概要：終点と境界を指定した prism は最後の垂直辺が可逆なら基底上で延長できる。
方針：反転して可逆な最初の辺を cocartesian とみなし、相対充填を二重反転で戻す。
規約：元・標的は quasicategory、p は inner fibration。
使われ方：Kerodon §7.1.5 の fiber の終対象による相対境界充填。 -/
lemma prism_lift_boundary_with_final_endpoint {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (n : ℕ)
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u}) ⟶ E)
    (F₁ : (Δ[n + 1] : SSet.{u}) ⟶ E)
    (β : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ B)
    (hF₁ : (boundary (n + 1)).ι ≫ F₁ = prismEndpoint 1 (boundary (n + 1) : SSet.{u}) ≫ H)
    (hHp : H ≫ p = (Δ[1] ◁ (boundary (n + 1)).ι) ≫ β)
    (hF₁p : F₁ ≫ p = prismEndpoint 1 Δ[n + 1] ≫ β)
    (hH : IsInvertibleEdge (edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (prismBoundaryLastVerticalEdge n)))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E,
      (Δ[1] ◁ (boundary (n + 1)).ι) ≫ F = H ∧
        prismEndpoint 1 Δ[n + 1] ≫ F = F₁ ∧ F ≫ p = β := by
  let RH := reverseBoundaryPrism H
  let RF₀ := (stdSimplex.opIso ⦋n + 1⦌).inv ≫ SSet.opFunctor.map F₁
  let Rβ := reverseStdPrism β
  have hR₀ : (boundary (n + 1)).ι ≫ RF₀ =
      prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ RH := by
    dsimp [RF₀, RH]
    rw [reverseBoundaryPrism_endpoint]
    change (boundary (n + 1)).ι ≫ (stdSimplex.opIso ⦋n + 1⦌).inv ≫ SSet.opFunctor.map F₁ =
      (boundaryReverseIso (n + 1)).hom ≫ SSet.opFunctor.map
        (prismEndpoint 1 (boundary (n + 1) : SSet.{u}) ≫ H)
    rw [← hF₁, SSet.opFunctor.map_comp,
      ← Category.assoc (boundaryReverseIso (n + 1)).hom,
      boundaryReverseIso_hom_ι, Category.assoc]
  have hRHp : RH ≫ SSet.opFunctor.map p = (Δ[1] ◁ (boundary (n + 1)).ι) ≫ Rβ := by
    dsimp [RH, Rβ]
    rw [← reverseBoundaryPrism_postcomp, hHp, ← reverseStdPrism_boundary]
  have hRF₀p : RF₀ ≫ SSet.opFunctor.map p = prismEndpoint 0 Δ[n + 1] ≫ Rβ := by
    dsimp [RF₀, Rβ]
    rw [Category.assoc, ← SSet.opFunctor.map_comp, hF₁p, reverseStdPrism_endpoint]
    rfl
  have he : HasCocartesianHornLifting (SSet.opFunctor.map p) (edgeOfSimplex
      (RH.app (Opposite.op ⦋1⦌) (prismBoundaryFirstVerticalEdge n))) :=
    (reverseBoundaryPrism_first_isInvertible n H hH).hasCocartesianHornLifting _
  obtain ⟨F', hF', hF'₀, hF'p⟩ := prism_lift_boundary_with_endpoint
    (SSet.opFunctor.map p) n RH RF₀ Rβ hR₀ hRHp hRF₀p he
  let F := reverseStdPrism F' ≫ (SSet.opFunctorCompOpFunctorIso.app E).hom
  refine ⟨F, ?_, ?_, ?_⟩
  · dsimp [F]
    rw [← Category.assoc, reverseStdPrism_boundary, hF']
    exact reverseBoundaryPrism_double H
  · dsimp [F]
    rw [← Category.assoc, reverseStdPrism_endpoint]
    have hrev : (1 : Fin 2).rev = 0 := by decide
    rw [hrev, hF'₀]
    dsimp [RF₀]
    have hnat := SSet.opFunctorCompOpFunctorIso.hom.naturality F₁
    change SSet.opFunctor.map (SSet.opFunctor.map F₁) ≫
      SSet.opFunctorCompOpFunctorIso.hom.app E =
        SSet.opFunctorCompOpFunctorIso.hom.app (Δ[n + 1] : SSet.{u}) ≫ F₁ at hnat
    simp only [SSet.opFunctor.map_comp, Category.assoc]
    rw [hnat]
    simpa only [Iso.app_hom, Category.assoc, Category.id_comp] using
      congrArg (fun t ↦ t ≫ F₁) (stdSimplex_doubleReverse.{u} (n + 1))
  · dsimp [F]
    have hnat := SSet.opFunctorCompOpFunctorIso.hom.naturality p
    change SSet.opFunctor.map (SSet.opFunctor.map p) ≫
      SSet.opFunctorCompOpFunctorIso.hom.app B =
        SSet.opFunctorCompOpFunctorIso.hom.app E ≫ p at hnat
    rw [Category.assoc, ← hnat, ← Category.assoc, ← reverseStdPrism_postcomp, hF'p]
    exact reverseStdPrism_double β

end SerrePositivity.InfinityCategories
