module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CartesianHomotopyExtension
public import SerrePositivity.InfinityCategories.F1.InvertibleCartesian
public import SerrePositivity.InfinityCategories.F1.MappingCylinderOverMono

/-!
概要：標準単体上の cartesian fibration を最初の fiber へ厳密に退縮する。
方針：最初の頂点への収縮を、fiber 上の定値 prism を固定して相対的に持ち上げる。
規約：元の包含・恒等射・底の収縮を保持。使われ方：始点 fiber の亜群化比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma prismFirstContraction_const_first (n : ℕ) (A : SSet.{u}) :
    (Δ[1] ◁ (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) : A ⟶ Δ[n])) ≫
      prismFirstContraction n = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro j
  change (if _ = 0 then (0 : Fin (n + 1)) else 0) = 0
  split_ifs <;> rfl

lemma exists_initialFiberRetraction (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ (Δ[n] : SSet.{u})) [CartesianFibration p] :
    ∃ (R : E ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))
      (H : (Δ[1] : SSet.{u}) ⊗ E ⟶ E),
      vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) ≫ R = 𝟙 _ ∧
      prismEndpoint 0 E ≫ H =
        R ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) ∧
      prismEndpoint 1 E ≫ H = 𝟙 E ∧
      H ≫ p = (Δ[1] ◁ p) ≫ prismFirstContraction n := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  let c := stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))
  let A := vertexFiber p c
  let i : A ⟶ E := vertexFiberι p c
  have : Mono i := by dsimp only [i]; infer_instance
  let H₀ : (Δ[1] : SSet.{u}) ⊗ A ⟶ E := snd Δ[1] A ≫ i
  let β : (Δ[1] : SSet.{u}) ⊗ E ⟶ Δ[n] := (Δ[1] ◁ p) ≫ prismFirstContraction n
  have h₁ : prismEndpoint 1 A ≫ H₀ = i ≫ 𝟙 E := by
    dsimp only [H₀]
    rw [← Category.assoc, prismEndpoint_snd, Category.id_comp, Category.comp_id]
  have hf : (𝟙 E) ≫ p = prismEndpoint 1 E ≫ β := by
    dsimp only [β]
    rw [Category.id_comp, ← Category.assoc, prismEndpoint_naturality,
      Category.assoc, prismFirstContraction_one, Category.comp_id]
  have hHp : H₀ ≫ p = (Δ[1] ◁ i) ≫ β := by
    dsimp only [H₀, β, i]
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, ← Category.assoc,
      ← whiskerLeft_comp, vertexFiberι_comp, prismFirstContraction_const_first]
  have hH : ∀ x : A _⦋0⦌, IsCartesianEdge p
      (H₀.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)) := by
    intro x
    have hi := isEquivalencePathVertex_const x.val
    unfold IsEquivalencePathVertex at hi
    rw [intervalFunctorVertexEdge_functorVertex] at hi
    exact isCartesianEdge_of_isInvertibleEdge p (edgeOfSimplex _) hi
  obtain ⟨H, hHi, hH₁, hHp, _⟩ :=
    HomotopyLimits.cartesianHomotopy_extend p i H₀ (𝟙 E) β h₁ hf hHp hH
  have h₀p : (prismEndpoint 0 E ≫ H) ≫ p = SSet.const c := by
    rw [Category.assoc, hHp]
    dsimp only [β]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      prismFirstContraction_zero, SSet.comp_const]
  let R := vertexFiberLift p c (prismEndpoint 0 E ≫ H) h₀p
  have hR : R ≫ i = prismEndpoint 0 E ≫ H := vertexFiberLift_ι _ _ _ _
  refine ⟨R, H, ?_, hR.symm, hH₁, hHp⟩
  apply vertexFiber_hom_ext p c
  change (i ≫ R) ≫ i = (𝟙 A) ≫ i
  rw [Category.assoc, hR, ← Category.assoc, ← prismEndpoint_naturality,
    Category.assoc, hHi]
  dsimp only [H₀]
  rw [← Category.assoc, prismEndpoint_snd, Category.id_comp]

end SerrePositivity.KST.LocalizingInvariants
