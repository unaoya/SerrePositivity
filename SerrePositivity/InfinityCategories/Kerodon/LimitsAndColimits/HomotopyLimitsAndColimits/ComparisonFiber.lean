module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.Detection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits

/-!
概要：写像空間の比較射の導来ファイバーと、その可縮性による極限の検出。
方針：可逆 path による置換の終点射の fiber を取り、同値なら全境界を充填する。
規約：置換前の比較射が fibration であるという仮定は置かない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の最後の可縮性の推論。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：比較射の終点を固定した可逆 path 置換の fiber。
方針：元の始域への trivial Kan fibration を持つ path 置換を使う。
規約：Kan 複体間ではホモトピーファイバーの模型として使う。任意の射で定義できる。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の比較射の導来ファイバー。 -/
noncomputable def comparisonFiber {A B : SSet.{u}} (q : A ⟶ B) (b : B _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q) b

/-- 概要：同値な quasicategory 間の比較射の path 置換の fiber は可縮。
方針：置換の終点射が trivial Kan fibration であることを既存の同値判定から得る。
規約：元の射の strict fiber の可縮性を主張するものではない。
使われ方：HTT 4.2.4.1 の双対で使う導来ファイバーの可縮性。 -/
lemma comparisonFiber_isContractibleKan_of_isQCatEquivalence {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (q : A ⟶ B) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence q)
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (comparisonFiber q b) := by
  have := hq.equivalencePathReplacementMap_trivialKanFibration
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q) b

/-- 概要：Kan 複体間の比較射がホモトピー同値なら導来ファイバーは可縮。
方針：ホモトピー逆を quasicategory の同値に変換して path 置換に適用する。
規約：比較射の fibration 性は要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の全ての対象 x での比較の帰結。 -/
lemma comparisonFiber_isContractibleKan_of_homotopyEquivalence {A B : SSet.{u}}
    [KanComplex A] [KanComplex B] (q : A ⟶ B)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence q) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (comparisonFiber q b) :=
  comparisonFiber_isContractibleKan_of_isQCatEquivalence q hq.isQCatEquivalence b

/-- 概要：全ての錐の写像空間を同値な比較射の導来ファイバーと同定できれば極限錐。
方針：比較射の同値から各 fiber の可縮性を証明し、厳密な同型で錐の写像空間へ移す。
規約：錐から fiber への同型と比較射の同値は入力であり、その構成は別の証明が必要。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、γ3b の実際の比較を接続する最後の推論。 -/
lemma isLimitCone_of_comparisonFiber_iso {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (A B : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p → SSet.{u})
    [∀ d, KanComplex (A d)] [∀ d, KanComplex (B d)]
    (q : ∀ d, A d ⟶ B d) (b : ∀ d, (B d) _⦋0⦌)
    (e : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) d c ≅ comparisonFiber (q d) (b d))
    (hq : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (q d)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isLimitCone_of_conePinchedHom_iso c _ e
    (fun d ↦ comparisonFiber_isContractibleKan_of_homotopyEquivalence (q d) (hq d) (b d))

/-- 概要：錐の写像空間と導来ファイバーのホモトピー同値から極限性を得る。
方針：同値な比較射の fiber の可縮性から Kan 性も得て、模型による検出を使う。
規約：fiber との厳密な同型は不要だが、全ての錐について比較の構成が必要。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の coherent な錐と homotopy 極限の比較の出口。 -/
lemma isLimitCone_of_comparisonFiber_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (A B : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p → SSet.{u})
    [∀ d, KanComplex (A d)] [∀ d, KanComplex (B d)]
    (q : ∀ d, A d ⟶ B d) (b : ∀ d, (B d) _⦋0⦌)
    (f : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) d c ⟶ comparisonFiber (q d) (b d))
    (hf : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f d))
    (hq : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (q d)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  have h (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (comparisonFiber (q d) (b d)) :=
    comparisonFiber_isContractibleKan_of_homotopyEquivalence (q d) (hq d) (b d)
  have (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) : KanComplex (comparisonFiber (q d) (b d)) := (h d).kanComplex
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isLimitCone_of_conePinchedHom_homotopyEquivalence c _ f hf h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
