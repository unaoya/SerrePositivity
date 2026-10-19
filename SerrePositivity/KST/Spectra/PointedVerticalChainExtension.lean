module

public import SerrePositivity.KST.Spectra.PointedVerticalChains
public import SerrePositivity.KST.Spectra.PointedRelativeHomotopyAdjustment

/-!
概要：部分対象上の元の垂直区間の有限鎖に沿い、点つき射を射影を固定して修正する。
方針：各区間を Kan fibration の相対ホモトピー延長へ入力し、全体の修正鎖を保持する。
規約：全単射への RLP は要求しない。使われ方：全列の相対厳密化の帰納段。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedExtension

/-- 部分対象上の垂直な有限鎖に沿って、元の射影を固定した全体の有限鎖を延長する。 -/
lemma exists_adjustment_chain_over {A T E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p.right)
    (i : A ⟶ T) [Mono i.right] (f : T ⟶ E) (a : A ⟶ E) (b : T ⟶ B)
    (hf : f ≫ p = b) (H : PointedMapping.VerticalChain p (i ≫ f) a) :
    ∃ g : T ⟶ E, i ≫ g = a ∧ g ≫ p = b ∧ PointedMapping.VerticalChain p f g := by
  induction H with
  | refl => exact ⟨f, rfl, hf, .refl⟩
  | @tail c d _ h ih =>
    obtain ⟨g, hg, hgp, hchain⟩ := ih
    obtain ⟨P⟩ := h
    have P' : PointedMapping.VerticalPath p (i ≫ g) d := by
      rw [hg]
      exact P
    have hgp' := congrArg Under.Hom.right hgp
    change g.right ≫ p.right = b.right at hgp'
    have hv : P'.homotopy.h ≫ p.right =
        fst A.right (Δ[1] : SSet.{u}) ≫ i.right ≫ b.right := by
      rw [P'.homotopy_over]
      change fst A.right (Δ[1] : SSet.{u}) ≫ (i.right ≫ g.right) ≫ p.right = _
      rw [Category.assoc, hgp']
    obtain ⟨g', hg', hgp'', V, hVB, _, hVP⟩ :=
      exists_homotopy_from_zero_over p hp i g d b hgp
        P'.homotopy P'.homotopy_base hv
    have hV : V.h ≫ p.right = fst T.right (Δ[1] : SSet.{u}) ≫ g.right ≫ p.right := by
      rw [hVP, hgp']
    exact ⟨g', hg', hgp'', hchain.tail
      ⟨PointedMapping.VerticalPath.ofHomotopy V hVB hV⟩⟩

end SerrePositivity.KST.Spectra.PointedExtension
