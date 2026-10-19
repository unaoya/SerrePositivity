module

public import SerrePositivity.InfinityCategories.F1B.InitialFixedContraction
public import SerrePositivity.InfinityCategories.F1B.KanFinalFiberRetraction
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianHomotopyEdges
public import SerrePositivity.InfinityCategories.F1.InvertibleCartesian

/-!
概要：始対象上の任意の図式を、cocartesian section の族へ厳密に延長する。
方針：始対象を固定した収縮を、指定した fiber 図式上で固定して cocartesian に持ち上げる。
規約：パラメータは任意の単体集合であり、評価の一致は厳密な等式。
使われ方：strict transport の fiber 評価の切断と相対境界充填の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始対象の fiber の図式を、その評価を固定して cocartesian section の族へ延長する。
方針：定値族を始対象の固定収縮に沿って輸送し、終点での辺の cocartesian 性を消去で示す。
規約：底は quasicategory、射影は cocartesian fibration。境界の指定はこの補題には含めない。
使われ方：始対象での評価の全パラメータにおける全射性。 -/
lemma exists_kanInitialSectionTransport {A T E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hv : IsInitialVertex v) (f : T ⟶ E)
    (hf : f ≫ p = SSet.const (a.app (Opposite.op ⦋0⦌) v)) :
    ∃ F : A ⊗ T ⟶ E,
      F ≫ p = fst A T ≫ a ∧ lift (SSet.const v) (𝟙 T) ≫ F = f ∧
      ∀ (x : T _⦋0⦌) (e : A _⦋1⦌), IsCocartesianEdge p
        (F.app (Opposite.op ⦋1⦌) (e, PinchedHom.constant x 1)) := by
  have : CocartesianHornFibration p := CocartesianFibration.toCocartesianHornFibration p
  have : Quasicategory E := quasicategory_of_innerFibration p
  obtain ⟨C, hC₀, hC₁, hCv⟩ := hv.exists_fixed_initial_prism
  let i : T ⟶ A ⊗ T := lift (SSet.const v) (𝟙 T)
  have : Mono i := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    intro x y h
    exact congrArg Prod.snd h
  let H₀ : (Δ[1] : SSet.{u}) ⊗ T ⟶ E := snd Δ[1] T ≫ f
  let f₀ : A ⊗ T ⟶ E := snd A T ≫ f
  let β : (Δ[1] : SSet.{u}) ⊗ (A ⊗ T) ⟶ B := (Δ[1] ◁ fst A T) ≫ C ≫ a
  have h₀ : prismEndpoint 0 T ≫ H₀ = i ≫ f₀ := by
    dsimp only [H₀, f₀, i]
    simp only [← Category.assoc, prismEndpoint_snd, Category.id_comp, lift_snd]
  have hf₀ : f₀ ≫ p = prismEndpoint 0 (A ⊗ T) ≫ β := by
    dsimp only [f₀, β]
    rw [Category.assoc, hf, SSet.comp_const, ← Category.assoc,
      prismEndpoint_naturality, Category.assoc, ← Category.assoc (prismEndpoint 0 A), hC₀,
      SSet.const_comp, SSet.comp_const]
  have hHp : H₀ ≫ p = (Δ[1] ◁ i) ≫ β := by
    dsimp only [H₀, β, i]
    rw [Category.assoc, hf, SSet.comp_const, ← Category.assoc, ← whiskerLeft_comp,
      lift_fst, ← Category.assoc (Δ[1] ◁ (SSet.const v : T ⟶ A)), hCv T, SSet.const_comp]
  have hH : ∀ x : T _⦋0⦌, HasCocartesianHornLifting p (edgeOfSimplex
      (H₀.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
    intro x
    have hi := isEquivalencePathVertex_const x
    unfold IsEquivalencePathVertex at hi
    rw [intervalFunctorVertexEdge_functorVertex] at hi
    exact (hi.map f).hasCocartesianHornLifting p
  obtain ⟨H, hHi, hH₀, hHp, hHc⟩ :=
    cocartesianHomotopy_extend p i H₀ f₀ β h₀ hf₀ hHp hH
  let F := prismEndpoint 1 (A ⊗ T) ≫ H
  have hFp : F ≫ p = fst A T ≫ a := by
    dsimp only [F]
    rw [Category.assoc, hHp]
    dsimp only [β]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      ← Category.assoc (prismEndpoint 1 A), hC₁, Category.id_comp]
  have hiF : i ≫ F = f := by
    dsimp only [F]
    rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc, hHi]
    dsimp only [H₀]
    rw [← Category.assoc, prismEndpoint_snd, Category.id_comp]
  refine ⟨F, hFp, hiF, ?_⟩
  intro x e
  let j : (Δ[1] : SSet.{u}) ⟶ A ⊗ T := lift (SSet.yonedaEquiv.symm e) (SSet.const x)
  have hs : j ≫ prismEndpoint 0 (A ⊗ T) ≫ H =
      SSet.const (f.app (Opposite.op ⦋0⦌) x) := by
    rw [hH₀]
    dsimp only [j, f₀]
    rw [← Category.assoc, lift_snd, SSet.const_comp]
  have hc := kanCocartesianHomotopy_targetEdge p H j
    (by rw [hs]; exact isCocartesianEdge_constant p _)
    (fun y ↦ (isCocartesianEdge_iff_hasCocartesianHornLifting p _).2 (hHc y))
  change IsCocartesianEdge p (SSet.yonedaEquiv (j ≫ F)) at hc
  change IsCocartesianEdge p (F.app (Opposite.op ⦋1⦌)
    ((SSet.yonedaEquiv.symm e).app _ (SSet.yonedaEquiv (𝟙 Δ[1])),
      PinchedHom.constant x 1)) at hc
  simpa only [SSet.yonedaEquiv_symm_app_id] using hc

end SerrePositivity.InfinityCategories
