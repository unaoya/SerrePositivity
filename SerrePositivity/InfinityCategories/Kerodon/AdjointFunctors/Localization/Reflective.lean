module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PointwiseUnitComparison

/-!
概要：充満部分複体への左随伴としての反射的部分 ∞ 圏。
方針：頂点条件で全部分複体を取り、包含への左随伴と反射単位を保持する。
規約：頂点条件の同型不変性は要求せず、局所対象は単位の可逆性で定義する。
使われ方：Kerodon §6.2.2（Tag 02F5）、Cor 6.2.2.26（Tag 02FF）、§6.3.3（Tag 02FY）、HTT §5.2.7 の反射的局所化。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-- 概要：頂点条件の張る充満部分 ∞ 圏への選んだ反射。
方針：包含への左随伴とその双圏随伴データを指定する。
規約：余単位の可逆性・冪等性・局所化の普遍性はフィールドに追加しない。
使われ方：B2 の反射からの一般性質の導出。 -/
structure ReflectiveSubcategory (X : SSet.{u}) [Quasicategory X] (P : X _⦋0⦌ → Prop) where
  reflector : X ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})
  adjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction reflector (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι

/-- 概要：頂点条件の充満部分 ∞ 圏が反射的であるという性質。
方針：選んだ反射のデータの存在で定義する。
規約：一般の局所化の存在を主張しない。使われ方：反射的部分圏の仮定。 -/
def IsReflectiveSubcategory (X : SSet.{u}) [Quasicategory X] (P : X _⦋0⦌ → Prop) : Prop :=
  Nonempty (ReflectiveSubcategory X P)

namespace ReflectiveSubcategory
variable {X : SSet.{u}} [Quasicategory X] {P : X _⦋0⦌ → Prop}
variable (r : ReflectiveSubcategory X P)

/-- 概要：反射を包含に続けた X の自己関手。
方針：充満部分圏に取った値を元の圏へ戻す。
規約：合成の順は X→部分圏→X。使われ方：局所化の冪等関手。 -/
def localization : X ⟶ X := r.reflector ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι

/-- 概要：反射の単位を h Fun(X,X) の射で保持する。
方針：選んだ随伴の単位を取り出す。
規約：成分ごとに新しい代表を選ばない。使われ方：局所対象と冪等性。 -/
def unit : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) r.localization := r.adjunction.unitHom

/-- 概要：反射単位が可逆な頂点としての局所対象。
方針：単位成分の hX の射の可逆性を要求する。
規約：P 自体に同型不変性を仮定しないため、P と同じ条件とは定義しない。
使われ方：反射の本質的な像との同定。 -/
def IsLocal (x : X _⦋0⦌) : Prop := IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x)

/-- 概要：反射の値は指定された充満部分圏の頂点条件を満たす。
方針：reflector の値の部分型の条件を読む。
規約：元の P への厳密な所属。使われ方：反射の標的の確認。 -/
lemma localization_mem (x : X _⦋0⦌) : P (r.localization.app (Opposite.op ⦋0⦌) x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (r.reflector.app (Opposite.op ⦋0⦌) x)

/-- 概要：反射部分圏の包含は写像空間の意味で充満忠実。
方針：全部分複体の包含の一般定理を適用する。
規約：h 圏の充満忠実性へ弱めない。使われ方：余単位の可逆性の導出。 -/
lemma inclusion_fullyFaithful (_r : ReflectiveSubcategory X P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι X P

/-- 概要：反射像から部分圏の対象への写像空間は元の対象からの写像空間に同値。
方針：充満部分圏の写像空間の厳密な同型の逆に随伴の pinched 比較を続ける。
規約：指定した部分圏の対象 y を標的とする。使われ方：反射の写像空間による普遍性。 -/
def reflectionMappingEquivalence (x : X _⦋0⦌)
    (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (r.localization.app (Opposite.op ⦋0⦌) x) y.val)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y.val) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.fullSubcomplexPinchedIso P (r.reflector.app (Opposite.op ⦋0⦌) x) y).symm).trans
    (r.adjunction.pinchedHomEquivalence x y)

end ReflectiveSubcategory
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
