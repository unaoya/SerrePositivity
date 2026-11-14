module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：left fibration の全ての頂点 fiber の Kan 性。
方針：左ホーン充填を反転して右ホーンによる Kan 判定に帰着し、fiber の普遍性で充填する。
規約：底の quasicategory 性を仮定しない。
使われ方：Kerodon Corollary 4.4.2.3（Tag 019E）、Construction 5.5.2.1（Tag 01ZW）、unstraightening の fiber 比較。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：全ての左ホーンを充填できる単体集合は Kan 複体。
方針：反転した単体集合の右ホーンを充填し、その全ホーン充填を元に戻す。
規約：左ホーンは正次元で最後の添字以外を持つ。
使われ方：Kerodon Corollary 4.4.2.3（Tag 019E）、left fibration の fiber の Kan 判定。 -/
lemma kanComplex_of_leftHornFillers (X : SSet.{u})
    (hf : ∀ (n : ℕ) (i : Fin (n + 2)), i < n + 1 →
      ∀ σ : (horn (n + 1) i : SSet.{u}) ⟶ X,
        ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (horn (n + 1) i).ι ≫ F = σ) : KanComplex X := by
  have : KanComplex X.op := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
    intro n i hi σ
    have hir : i.rev < n + 1 := by
      change i.rev.val < n + 1
      rw [Fin.val_rev]
      change 0 < i.val at hi
      omega
    let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap (n + 1) i σ ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
    obtain ⟨F, hF⟩ := hf n i.rev hir τ
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornFiller_of_reverseHornFiller (n + 1) i σ
      (F ≫ (SSet.opFunctorCompOpFunctorIso.app X).inv)
    rw [← Category.assoc, hF]
    dsimp only [τ]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ σ
  obtain ⟨F, hF⟩ := KanComplex.hornFilling (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap (n + 1) i σ)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornFiller_of_reverseHornFiller (n + 1) i σ F hF.symm

/-- 概要：left fibration の頂点上の fiber は Kan 複体。
方針：fiber の左ホーンを元へ含め、下を定値にして持ち上げ、fiber へ戻す。
規約：元と底の quasicategory 性は不要。
使われ方：Kerodon Corollary 4.4.2.3（Tag 019E）、𝒮 値 unstraightening の fiber の Kan 性。 -/
@[kerodon 019E]
lemma vertexFiber_kanComplex_of_leftFibration {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := by
  apply kanComplex_of_leftHornFillers
  intro n i hi a
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i hi)
  have sq : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (horn (n + 1) i).ι p (SSet.const b) := by
    constructor
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b sq.lift sq.fac_right, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  exact sq.fac_left

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.5.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.kanComplex_of_leftHornFillers
