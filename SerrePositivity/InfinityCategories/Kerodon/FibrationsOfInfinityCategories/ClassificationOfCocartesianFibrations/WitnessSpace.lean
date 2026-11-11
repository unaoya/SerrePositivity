module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration

/-!
概要：空間値 transport representation の選択空間と底変換への制限。
方針：実際の表現を表す頂点が張る全部分複体を取り、四角形の制限を持ち上げる。
規約：Kan 性、可縮性、境界固定延長の存在は別の証明課題。
使われ方：Kerodon §§5.6.8（Tag 02S9）–5.6.9（Tag 02SM）、相対表現の延長を検査する選択空間。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance transportWitnessPullbackLeftFibration {E B D : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：四角形の空間の頂点が実際の transport representation を表す条件。
方針：分類図式と pointed space への射を保つ頂点表示を使う。
規約：表現の fiber ごとの同値性を含む条件。
使われ方：Kerodon §5.6.8（Tag 02S9）、選択空間の全部分複体の頂点条件。 -/
def IsTransportWitnessVertex {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p) _⦋0⦌) : Prop :=
  ∃ R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex R.toSquare = v

/-- 概要：空間値の transport representation の全次数の選択空間。
方針：表現を表す頂点が張る四角形の空間の全部分複体を取る。
規約：表現の存在は定義に仮定しない。
使われ方：Kerodon §5.6.8（Tag 02S9）、空間値 transport witnesses。 -/
noncomputable def transportWitnessSpace {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    SSet.{u + 1} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p) (IsTransportWitnessVertex p) : SSet.{u + 1})

/-- 概要：表現の選択空間から周囲の四角形の空間への包含。
方針：全部分複体の包含を取る。
規約：高次単体も保つ単射。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、制限写像の比較図式。 -/
noncomputable def transportWitnessSpaceι {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    transportWitnessSpace p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p) (IsTransportWitnessVertex p)).ι

/-- 概要：表現の選択空間は quasicategory。
方針：四角形の quasicategory の全部分複体の判定を使う。
規約：Kan 性や非空性をこの段階で仮定しない。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現間の比較のホモトピー圏。 -/
instance transportWitnessSpace_quasicategory {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : Quasicategory (transportWitnessSpace p) :=
  inferInstanceAs (Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p) (IsTransportWitnessVertex p) : SSet.{u + 1}))

/-- 概要：表現の実際のデータを選択空間の頂点へ写す。
方針：可換四角形の頂点に、表現を表すという条件を添える。
規約：分類図式と全空間の射をともに保つ。
使われ方：Kerodon §5.6.8（Tag 02S9）、境界上で指定された表現の入力。 -/
noncomputable def transportWitnessVertex {E B : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) :
    (transportWitnessSpace p) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex R.toSquare, by
    intro v
    obtain rfl : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    simpa only [op_id, Functor.map_id_apply] using
      (show IsTransportWitnessVertex p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex R.toSquare) from ⟨R, rfl⟩)⟩

/-- 概要：選択空間の全ての頂点は実際の表現のデータから得られる。
方針：全部分複体の頂点条件の存在を取り出す。
規約：射の等式まで回収する。
使われ方：Kerodon §5.6.8（Tag 02S9）、選択空間の頂点の解釈。 -/
lemma transportWitnessVertex_surjective {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    Function.Surjective (transportWitnessVertex (p := p)) := by
  intro v
  obtain ⟨R, h⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
  exact ⟨R, Subtype.ext h⟩

/-- 概要：表現の選択空間の頂点表示は単射。
方針：四角形の頂点の単射性と表現の両射による外延性を使う。
規約：fiber 同値性の証明の選択は頂点を変えない。
使われ方：Kerodon §5.6.8（Tag 02S9）、境界上の厳密なデータの同定。 -/
lemma transportWitnessVertex_injective {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    Function.Injective (transportWitnessVertex (p := p)) := by
  intro R S h
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_injective p (congrArg Subtype.val h)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation.ext R S (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare.diagram hs)
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare.pointedMap hs)

/-- 概要：実際の表現のデータと選択空間の頂点は全単射。
方針：構成した頂点表示の単射性と全射性を使う。
規約：単なる同値類の対応ではない。
使われ方：Kerodon Theorem 5.6.5.12（Tag 0293）、選択空間の持ち上げから表現の延長を回収する。 -/
noncomputable def transportWitnessVertexEquiv {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p ≃ (transportWitnessSpace p) _⦋0⦌ :=
  Equiv.ofBijective transportWitnessVertex
    ⟨transportWitnessVertex_injective p, transportWitnessVertex_surjective p⟩

/-- 概要：transport witnesses の底変換への制限。
方針：四角形の制限を全部分複体へ持ち上げ、実際の表現の制限で頂点条件を示す。
規約：任意の底の射 g を許す。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、相対延長で用いる制限写像。 -/
noncomputable def transportWitnessRestriction {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) :
    transportWitnessSpace p ⟶ transportWitnessSpace (pullback.snd p g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (IsTransportWitnessVertex (pullback.snd p g))
    (transportWitnessSpaceι p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g) (by
      intro v
      obtain ⟨R, rfl⟩ := transportWitnessVertex_surjective p v
      refine ⟨R.restrict g, ?_⟩
      change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex (R.restrict g).toSquare =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex R.toSquare)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_vertex, R.restrict_toSquare g])

/-- 概要：表現空間の制限は周囲の四角形の制限と可換。
方針：全部分複体への持ち上げの包含公式を使う。
規約：全次数の厳密な等式。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK） の周囲の比較四角形。 -/
lemma transportWitnessRestriction_ι {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) :
    transportWitnessRestriction p g ≫ transportWitnessSpaceι (pullback.snd p g) =
      transportWitnessSpaceι p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：選択空間の制限は頂点で実際の表現の厳密な制限を回収する。
方針：全部分複体の値で四角形の制限公式を使う。
規約：分類図式と全空間の射を同時に保つ。
使われ方：Kerodon Theorem 5.6.5.12（Tag 0293）、制限写像の持ち上げから表現の延長を回収する。 -/
lemma transportWitnessRestriction_vertex {E B D : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (g : D ⟶ B) :
    (transportWitnessRestriction p g).app _ (transportWitnessVertex R) =
      transportWitnessVertex (R.restrict g) := by
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex R.toSquare) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex (R.restrict g).toSquare
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_vertex, R.restrict_toSquare g]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
