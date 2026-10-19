module
public import SerrePositivity.KST.SConstruction.McCarthyThetaEndpoints
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # McCarthy の左 fiber の quotient 射の弱同値
概要：quotient 射は構成した切断を局所化で逆に持つ。
方針：ρ と θ の二つの実単体ホモトピーを anodyne 局所化で等号に送る。
規約：左 fiber の Kan 性や単一の連結ホモトピーを仮定しない。使われ方：単体積版 Quillen A。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：左 fiber の quotient と切断の合成は anodyne 局所化で恒等射。
方針：ρ の恒等端点から終端へ、θ で終端から切断との合成へ移る二つのホモトピー。
規約：同じ左 fiber 内の構成済みホモトピーだけを使う。使われ方：quotient の逆射の検証。 -/
lemma mcCarthyFiber_retraction_localized (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    AnodyneHomotopy.anodyneQ.map (cofiberLeftFiberQuotient X a ≫ mcCarthyFiberSection X a) =
      𝟙 (AnodyneHomotopy.anodyneQ.obj (cofiberSubobjectLeftFiber X a)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hQ := Localization.inverts Q SSet.anodyneExtensions
  have hρ := AnodyneHomotopy.map_homotopy_eq Q hQ (mcCarthyRhoFiberHomotopy X a)
  have hθ := AnodyneHomotopy.map_homotopy_eq Q hQ (mcCarthyThetaFiberHomotopy X a)
  exact ((hρ.trans hθ).symm).trans (Q.map_id _)

/-- 概要：左 fiber の quotient 射は anodyne 局所化で同型。
方針：標準 ι 型の切断を逆射とし、厳密な片側逆と二ホモトピーによる反対側逆を照合する。
規約：追加の弱同値・加法性仮定は不要。使われ方：Fiore–Pieper の単体積版 Quillen A の入力。 -/
lemma cofiberLeftFiberQuotient_localized_isIso (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    IsIso (AnodyneHomotopy.anodyneQ.map (cofiberLeftFiberQuotient X a)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  refine ⟨⟨Q.map (mcCarthyFiberSection X a), ?_, ?_⟩⟩
  · exact (Q.map_comp _ _).symm.trans (mcCarthyFiber_retraction_localized X a)
  · rw [← Q.map_comp, mcCarthyFiberSection_quotient, Q.map_id]

end SerrePositivity.KST.SConstruction
