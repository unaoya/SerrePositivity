module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeHomotopyTransport

/-! # Left fibration に沿う任意パラメーターの prism の持ち上げ

概要：先頭で与えた写像から、底の任意パラメーターの区間族を left fibration へ持ち上げる。
方針：先頭一次ホーンとパラメーターの積の左非輪状性を使い、因子の順序を交換する。
規約：パラメーターや底の quasicategory 性は不要。使われ方：余錐空間の終点輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：Left fibration に沿って、任意の底の区間族を指定した先頭から持ち上げられる。
方針：一次ホーンの prism の持ち上げを因子交換で通常の区間族へ戻す。
規約：先頭写像と底の族を厳密に保持する。使われ方：fiber 全体の輸送の構成。 -/
lemma leftFibration_prism_lift {A E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (s : A ⟶ E) (H : A ⊗ (Δ[1] : SSet.{u}) ⟶ B) (h₀ : SSet.ι₀ ≫ H = s ≫ p) :
    ∃ R : A ⊗ (Δ[1] : SSet.{u}) ⟶ E, SSet.ι₀ ≫ R = s ∧ R ≫ p = H := by
  let D := (β_ (Δ[1] : SSet.{u}) A).hom ≫ H
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_point_whiskerRight A p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))
  have sq : CommSq (snd (horn 1 0 : SSet.{u}) A ≫ s) ((horn 1 0).ι ▷ A) p D := by
    constructor
    dsimp [D]
    rw [Category.assoc, ← h₀, ← Category.assoc ((horn 1 0).ι ▷ A),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization, Category.assoc, Category.assoc]
    rfl
  let R := (β_ A (Δ[1] : SSet.{u})).hom ≫ sq.lift
  refine ⟨R, ?_, ?_⟩
  · have hL₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ sq.lift = s := by
      have h := congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection A ≫ t) sq.fac_left
      simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_snd,
        Category.id_comp] using h
    dsimp [R]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding A, Category.assoc, ← Category.assoc
      (β_ (Δ[1] : SSet.{u}) A).hom, SymmetricCategory.symmetry, Category.id_comp]
    exact hL₀
  · dsimp [R]
    rw [Category.assoc, sq.fac_right]
    dsimp [D]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
