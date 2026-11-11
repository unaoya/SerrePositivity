module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.TransportConeAssembly

/-!
概要：元の射影の切断を各 under 圏へ制限して strict transport 図式の通常の錐を作る。
方針：切断の普遍的な族を under の忘却関手で前合成し、相対関手へ curry する。
規約：全空間と底の充填性は要求しない。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の strict transport の極限錐。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {I : Type u} [SmallCategory I] {E : SSet.{u}}

/-- 概要：元の切断の族を i の under 圏へ制限した strict transport の値への射。
方針：忘却関手の nerve で第一変数を制限し、相対関手空間へ curry する。
規約：パラメータは元の射影の切断空間。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.4.1.6（Tag 05QS） の strict transport の錐の成分。 -/
noncomputable def transportSectionsRestriction (p : E ⟶ nerve I) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport p i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (p := p) (a := nerveMap (Under.forget i))
    ((nerveMap (Under.forget i) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection, whiskerRight_fst])

/-- 概要：under 圏への制限の評価は普遍的な切断の族の第一変数の前合成である。
方針：相対 curry と uncurry の逆関係を使う。
規約：元の全空間への射の等式として述べる。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.4.1.6（Tag 05QS） の錐の成分の具体的な評価式。 -/
lemma transportSectionsRestriction_evaluation (p : E ⟶ nerve I) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (transportSectionsRestriction p i) =
      (nerveMap (Under.forget i) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry _ _

/-- 概要：under 圏への切断の制限は strict transport の構造射と可換である。
方針：評価の単射性で第一変数の前合成に移し、under の忘却の可換性を使う。
規約：図式の全ての射について厳密に可換。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.4.1.6（Tag 05QS） の通常の錐の自然性。 -/
lemma transportSectionsRestriction_naturality (p : E ⟶ nerve I) {i j : I} (f : i ⟶ j) :
    transportSectionsRestriction p i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMap p f =
      transportSectionsRestriction p j := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p (nerveMap (Under.forget j))
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMap p f = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p
    (nerveMap (Under.forget i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) from rfl]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, transportSectionsRestriction_evaluation,
    transportSectionsRestriction_evaluation, ← Category.assoc, ← comp_whiskerRight,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection]

/-- 概要：切断空間は strict transport 図式の通常の錐を担う。
方針：under 圏への全ての制限とその自然性をまとめる。
規約：この定義には極限性の証明は含めない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断と strict transport の極限の同定。 -/
noncomputable def transportSectionsCone (p : E ⟶ nerve I) :
    Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p
  π := { app := transportSectionsRestriction p
         naturality := fun i j f => by
           change 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) ≫ transportSectionsRestriction p j =
             transportSectionsRestriction p i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMap p f
           rw [Category.id_comp]
           exact (transportSectionsRestriction_naturality p f).symm }

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
