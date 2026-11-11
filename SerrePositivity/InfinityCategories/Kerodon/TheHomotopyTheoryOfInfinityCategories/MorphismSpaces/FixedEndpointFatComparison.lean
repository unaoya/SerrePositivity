module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedEndpointConeIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan

/-!
概要：固定頂点の内部 Hom の錐と両端固定の fat join の錐の比較の同値性。
方針：二重 fiber の同型の後で、既存の両端固定の fat join 比較の同値を適用する。
規約：頂点も図式も厳密に固定し、標的 X の quasicategory 性だけを仮定する。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の共通の錐の模型の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：join の両端の包含は全ての頂点を含む。
方針：頂点の切断が零か一かに分け、それぞれ右端と左端から回収する。
規約：左右の因子の非空性を要求しない。
使われ方：Kerodon §4.6.6（Tag 04HY）、両端固定の錐の関手空間の Kan 性。 -/
lemma joinEndpointInclusion_vertex_surjective (A B : SSet.{u}) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion A B).app (Opposite.op ⦋0⦌)) := by
  rintro ⟨r, a, b⟩
  fin_cases r
  · refine ⟨Sum.inr b, ?_⟩
    cases a
    rfl
  · refine ⟨Sum.inl a, ?_⟩
    cases b
    rfl

/-- 概要：両端を固定した join の錐の関手空間は Kan 複体。
方針：両端包含が単射で全頂点を含むことを関手空間の固定 fiber の Kan 判定に使う。
規約：K は任意、X に quasicategory 性だけを要求する。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の固定頂点の錐の空間。 -/
instance fixedEndpointConeSpace_kanComplex {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeSpace p x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_preFiber_of_vertexSurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion Δ[0] K)
    (joinEndpointInclusion_vertex_surjective Δ[0] K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))

/-- 概要：内部 Hom の錐の頂点 fiber は Kan 複体。
方針：両端固定の単一 fiber の Kan 性を厳密な同型で移す。
規約：X の Kan 性ではなく quasicategory 性だけを要求する。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.4.1.6（Tag 05QS） の切断空間との比較の標的。 -/
instance fixedApexConeFamily_kanComplex {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily p x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexEndpointConeSpaceIso p x).symm

/-- 概要：頂点と図式を固定した fat join の錐の関手空間。
方針：fat join の両端包含からの制限の fiber を取る。
規約：端点の図式は通常の join の模型と共通である。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の二つの錐の模型の共通の比較先。 -/
noncomputable def fixedEndpointFatConeSpace {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))

/-- 概要：両端固定の fat join の錐の関手空間は quasicategory。
方針：両端包含の単射性により制限が inner fibration であることを使う。
規約：X の quasicategory 性だけを要求する。
使われ方：Kerodon §4.6.6（Tag 04HY）、両端固定の比較の圏同値性の標的。 -/
instance fixedEndpointFatConeSpace_quasicategory {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : Quasicategory (fixedEndpointFatConeSpace p x) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))))

/-- 概要：両端固定の通常の join の錐を fat join の錐へ移す標準比較。
方針：fat join 比較による前合成を同じ両端の fiber へ制限する。
規約：図式と頂点の両方を保つ実際の射である。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定頂点の模型間の比較。 -/
noncomputable def fixedEndpointConeFatComparison {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeSpace p x ⟶ fixedEndpointFatConeSpace p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[0] : SSet.{u}) K)).app X)
    (by rw [← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion_comparison])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))

/-- 概要：両端固定の通常の join と fat join の錐の標準比較は圏同値。
方針：既存の両端固定の fat join 比較を指定された端点の図式に適用する。
規約：X は quasicategory、K と p と x は任意である。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の固定条件の下で使える同値。 -/
lemma fixedEndpointConeFatComparison_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (fixedEndpointConeFatComparison p x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_fatJoinComparison_fixedEndpoints Δ[0] K X
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p)

/-- 概要：内部 Hom の固定頂点の錐から両端固定の fat join の錐への標準比較。
方針：二重 fiber の厳密な同型と両端固定の fat join 比較を合成する。
規約：頂点と図式を保つ射であり、逆射の選択は含まない。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.4.1.6（Tag 05QS） の切断空間との比較の準備。 -/
noncomputable def fixedApexFatConeComparison {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily p x ⟶ fixedEndpointFatConeSpace p x :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexEndpointConeSpaceIso p x).hom ≫ fixedEndpointConeFatComparison p x

/-- 概要：内部 Hom の固定頂点の錐と両端固定の fat join の錐の比較は圏同値。
方針：厳密な同型と既存の両端固定の同値を合成する。
規約：任意の K と図式 p に対し X の quasicategory 性だけで成立する。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の固定頂点を保った模型の同値。 -/
lemma fixedApexFatConeComparison_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (fixedApexFatConeComparison p x) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexEndpointConeSpaceIso p x)).isQCatEquivalence.comp
    (fixedEndpointConeFatComparison_isQCatEquivalence p x)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
