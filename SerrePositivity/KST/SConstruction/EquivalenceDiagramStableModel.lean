module
public import SerrePositivity.KST.SConstruction.EquivalenceDiagramEvaluation
public import SerrePositivity.KST.SConstruction.ObjectSTrivialFibration

/-! # D(m,w) の安定性と object S の行の弱同値
概要：全同値図式の圏を安定な入力として束ね、定数図式への包含の object S の像が弱同値と示す。
方針：零頂点での評価の自明ファイブレーションで安定性と完全性を移し、厳密な切断を使う。
規約：元の object/core 比較の弱同値はまだ含まない。使われ方：Fiore–Pieper Proposition 4.27。
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

/-- 概要：安定な C の全同値な標準単体図式の圏も安定。
方針：零頂点での評価の trivial Kan fibration により反映する。
規約：零次数も含む。使われ方：object S を適用する入力。 -/
instance equivalenceDiagrams_isStable (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (equivalenceDiagrams (Δ[n] : SSet.{u}) C) :=
  isStable_of_trivialKanFibration
    (equivalenceDiagramEvaluation Δ[n] C (stdSimplex.obj₀Equiv.symm 0))

/-- 概要：D(m,w) を安定な入力としてまとめる。
方針：全同値図式の quasicategory 性と安定性を添える。
規約：全同値な図式全体を使う。使われ方：行方向の object S。 -/
def equivalenceDiagramStableModel (n : ℕ) (X : StableModel.{u}) : StableModel.{u} :=
  { carrier := equivalenceDiagrams (Δ[n] : SSet.{u}) X.carrier
    quasicategory := inferInstance
    stable := inferInstance }

/-- 概要：零頂点での評価は安定な入力間の完全関手。
方針：自明ファイブレーションは零対象と全押し出しを保つ。
規約：底の射は評価そのもの。使われ方：object S のホモトピー逆。 -/
def equivalenceDiagramStableEvaluation (n : ℕ) (X : StableModel.{u}) :
    equivalenceDiagramStableModel n X ⟶ X :=
  ⟨equivalenceDiagramEvaluation Δ[n] X.carrier (stdSimplex.obj₀Equiv.symm 0),
    (preservesSConstructionData_of_trivialKanFibration _).toCofiberData⟩

/-- 概要：定数図式への包含も安定な入力間の完全関手。
方針：評価の厳密な切断なので普遍性の反映から完全性を得る。
規約：定数図式の射を使い、別の切断は選ばない。使われ方：元の行の比較。 -/
def equivalenceDiagramStableConstant (n : ℕ) (X : StableModel.{u}) :
    X ⟶ equivalenceDiagramStableModel n X :=
  ⟨equivalenceDiagramConstant Δ[n] X.carrier,
    (preservesSConstructionData_section_of_trivialKanFibration
      (equivalenceDiagramEvaluation Δ[n] X.carrier (stdSimplex.obj₀Equiv.symm 0))
      (equivalenceDiagramConstant Δ[n] X.carrier)
      (equivalenceDiagramConstant_evaluation Δ[n] X.carrier
        (stdSimplex.obj₀Equiv.symm 0))).toCofiberData⟩

/-- 概要：定数図式を評価する合成は完全関手としても恒等射。
方針：底の厳密な切断の式を使う。
規約：保存条件の証明は証明無関係性で一致。使われ方：object S の後の切断の式。 -/
lemma equivalenceDiagramStableConstant_evaluation (n : ℕ) (X : StableModel.{u}) :
    equivalenceDiagramStableConstant n X ≫ equivalenceDiagramStableEvaluation n X = 𝟙 X :=
  Subtype.ext (equivalenceDiagramConstant_evaluation Δ[n] X.carrier
    (stdSimplex.obj₀Equiv.symm 0))

/-- 概要：D(m,w) の評価の object S の像は局所化で同型。
方針：評価の実際の trivial Kan fibration に object S の保存定理を適用する。
規約：object/core 比較は仮定しない。使われ方：行のホモトピー逆。 -/
lemma equivalenceDiagramStableEvaluation_objectS_localized_isIso (n : ℕ)
    (X : StableModel.{u}) : IsIso (AnodyneHomotopy.anodyneQ.map
      (objectSConstructionFunctor.map (equivalenceDiagramStableEvaluation n X))) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (equivalenceDiagramStableEvaluation n X).val :=
    equivalenceDiagramEvaluation_trivialKanFibration n X.carrier
  exact objectS_map_localized_isIso_of_trivialKanFibration
    (equivalenceDiagramStableEvaluation n X)

/-- 概要：定数図式への包含の object S の像は局所化で同型。
方針：評価との合成は厳密に恒等射で、評価の像は既に同型。
規約：全ての行の次数で成立。使われ方：core S の二重単体集合との行の比較。 -/
lemma equivalenceDiagramStableConstant_objectS_localized_isIso (n : ℕ)
    (X : StableModel.{u}) : IsIso (AnodyneHomotopy.anodyneQ.map
      (objectSConstructionFunctor.map (equivalenceDiagramStableConstant n X))) := by
  let F := objectSConstructionFunctor ⋙ AnodyneHomotopy.anodyneQ.{u}
  have : IsIso (F.map (equivalenceDiagramStableEvaluation n X)) :=
    equivalenceDiagramStableEvaluation_objectS_localized_isIso n X
  have : IsIso (F.map (equivalenceDiagramStableConstant n X) ≫
      F.map (equivalenceDiagramStableEvaluation n X)) := by
    rw [← F.map_comp, equivalenceDiagramStableConstant_evaluation, F.map_id]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.map (equivalenceDiagramStableConstant n X))
    (F.map (equivalenceDiagramStableEvaluation n X))

end SerrePositivity.KST.SConstruction
