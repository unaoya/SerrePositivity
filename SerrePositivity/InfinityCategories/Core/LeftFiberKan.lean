module

public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Opposite
public import SerrePositivity.InfinityCategories.Core.MappingSpaceRightKan

/-!
概要：left fibration の全ての頂点 fiber の Kan 性。
方針：左ホーン充填を反転して右ホーンによる Kan 判定に帰着し、fiber の普遍性で充填する。
規約：底の quasicategory 性を仮定しない。
使われ方：Kerodon Corollary 4.4.2.3、Construction 5.5.2.1、unstraightening の fiber 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：全ての左ホーンを充填できる単体集合は Kan 複体。
方針：反転した単体集合の右ホーンを充填し、その全ホーン充填を元に戻す。
規約：左ホーンは正次元で最後の添字以外を持つ。
使われ方：Kerodon Corollary 4.4.2.3、left fibration の fiber の Kan 判定。 -/
lemma kanComplex_of_leftHornFillers (X : SSet.{u})
    (hf : ∀ (n : ℕ) (i : Fin (n + 2)), i < n + 1 →
      ∀ σ : (horn (n + 1) i : SSet.{u}) ⟶ X,
        ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (horn (n + 1) i).ι ≫ F = σ) : KanComplex X := by
  have : KanComplex X.op := by
    apply kanComplex_of_rightHornFillers
    intro n i hi σ
    have hir : i.rev < n + 1 := by
      change i.rev.val < n + 1
      rw [Fin.val_rev]
      change 0 < i.val at hi
      omega
    let τ := reverseHornMap (n + 1) i σ ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
    obtain ⟨F, hF⟩ := hf n i.rev hir τ
    apply hornFiller_of_reverseHornFiller (n + 1) i σ
      (F ≫ (SSet.opFunctorCompOpFunctorIso.app X).inv)
    rw [← Category.assoc, hF]
    dsimp only [τ]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply kanComplex_of_rightHornFillers
  intro n i _ σ
  obtain ⟨F, hF⟩ := KanComplex.hornFilling (reverseHornMap (n + 1) i σ)
  exact hornFiller_of_reverseHornFiller (n + 1) i σ F hF.symm

/-- 概要：left fibration の頂点上の fiber は Kan 複体。
方針：fiber の左ホーンを元へ含め、下を定値にして持ち上げ、fiber へ戻す。
規約：元と底の quasicategory 性は不要。
使われ方：Kerodon Corollary 4.4.2.3、𝒮 値 unstraightening の fiber の Kan 性。 -/
lemma vertexFiber_kanComplex_of_leftFibration {E B : SSet.{u}} (p : E ⟶ B)
    [LeftFibration p] (b : B _⦋0⦌) : KanComplex (vertexFiber p b) := by
  apply kanComplex_of_leftHornFillers
  intro n i hi a
  have := LeftFibration.mem (p := p) _ (leftHornInclusions.intro i hi)
  have sq : CommSq (a ≫ vertexFiberι p b) (horn (n + 1) i).ι p (SSet.const b) := by
    constructor
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  refine ⟨vertexFiberLift p b sq.lift sq.fac_right, ?_⟩
  apply vertexFiber_hom_ext p b
  rw [Category.assoc, vertexFiberLift_ι]
  exact sq.fac_left

end SerrePositivity.InfinityCategories
