module
public import SerrePositivity.KST.SConstruction.RelativeMcCarthyTheta
public import SerrePositivity.KST.SConstruction.SimplicialProductQuillenA

/-! # 相対左 fiber の quotient の弱同値
概要：相対 quotient は構成した切断を局所化後の逆射に持つ。
方針：同じ相対 fiber 内の ρ・θ の二ホモトピーと厳密な右逆を照合する。
規約：周囲の弱同値の制限からは結論しない。使われ方：相対加法性の Quillen A の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 相対 quotient と切断の反対側の合成は局所化後に恒等射。 -/
lemma relativeMcCarthyFiber_retraction_localized {X : StableModel.{u}}
    (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    AnodyneHomotopy.anodyneQ.map
      (relativeCofiberLeftFiberQuotient A B a ≫ relativeMcCarthyFiberSection A B a) =
    𝟙 (AnodyneHomotopy.anodyneQ.obj (relativeCofiberSubobjectLeftFiber A B a)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hQ := Localization.inverts Q SSet.anodyneExtensions
  have hρ := AnodyneHomotopy.map_homotopy_eq Q hQ (relativeMcCarthyRhoHomotopy A B a)
  have hθ := AnodyneHomotopy.map_homotopy_eq Q hQ (relativeMcCarthyThetaHomotopy A B a)
  exact ((hρ.trans hθ).symm).trans (Q.map_id _)

/-- 相対左 fiber から B の object S への元の quotient は局所化同型。 -/
lemma relativeCofiberLeftFiberQuotient_localized_isIso {X : StableModel.{u}}
    (A B : ClosedStablePredicate X) {m : ℕ}
    (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeCofiberLeftFiberQuotient A B a)) := by
  let Q := AnodyneHomotopy.anodyneQ
  refine ⟨⟨Q.map (relativeMcCarthyFiberSection A B a), ?_, ?_⟩⟩
  · exact (Q.map_comp _ _).symm.trans (relativeMcCarthyFiber_retraction_localized A B a)
  · rw [← Q.map_comp, relativeMcCarthyFiberSection_quotient, Q.map_id]

end SerrePositivity.KST.SConstruction
