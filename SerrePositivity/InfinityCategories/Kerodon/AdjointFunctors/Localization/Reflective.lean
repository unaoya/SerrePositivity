module


public meta import SerrePositivity.Util.Citation
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

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.2.7.2" (partial := special) "仮定：頂点条件 P による充満部分準圏への反射 r（Lean が強い：右随伴が充満包含として与えられる場合）。結論：r.reflector が、充満忠実な右随伴である包含を持つ局所化関手（この場合に HTT の定義と一致）。任意の辺反転による IsLocalization は原典のこの狭い意味と区別し、その定義を代用しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory
attribute [cite HTT "5.2.7.2" (partial := special) "仮定：頂点条件 P による充満部分準圏への反射 r（Lean が強い：右随伴が充満包含として与えられる場合）。結論：r.reflector が、充満忠実な右随伴である包含を持つ局所化関手（この場合に HTT の定義と一致）。任意の辺反転による IsLocalization は原典のこの狭い意味と区別し、その定義を代用しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.inclusion_fullyFaithful
attribute [cite HTT "5.2.7.4" (partial := direction) "仮定：充満部分圏への反射で L は reflector と包含の合成（原典の (2) を満たす場合）。結論：同じ単位 α の αL と Lα の全自然同型、すなわち (3)（Lean が弱い：(2)⇒(3) の向き）。Lα は reflectedUnitIso を包含で後合成して得る。(3) だけから反射を構成する向きや三条件の同値は主張しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.localization
attribute [cite HTT "5.2.7.6" (partial := special) "仮定：反射 r と対象 x、局所化射には同じ反射の単位成分を取る（Lean が強い：任意の指定射ではなく反射単位の場合）。結論：全 y∈P について MapC(rx,y)→MapC(x,y) の同値であり、この単位が P に関する局所化射（この場合に定義の条件と一致）。随伴の標準単位比較との同型もあり、無関係な写像空間の同値を選んだものではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.reflectionMappingEquivalence
attribute [cite HTT "5.2.7.8" (partial := direction) "仮定：P の包含への左随伴が存在する（原典の (2)、Lean はそのデータ r を取る）。結論：同じ単位が各 x の局所化射を与える（Lean が弱い：(2)⇒(1) の向き）。写像空間の同値でその普遍性を与える。各対象ごとの局所化射から全左随伴を構成する逆方向は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.reflectionMappingEquivalence
attribute [cite HTT "5.2.7.8" (partial := direction) "仮定：P の包含への左随伴が存在する（原典の (2)、Lean はそのデータ r を取る）。結論：同じ単位が各 x の局所化射を与える（Lean が弱い：(2)⇒(1) の向き）。写像空間の同値でその普遍性を与える。各対象ごとの局所化射から全左随伴を構成する逆方向は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.unit
attribute [cite HTT "5.2.7.9"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsReflectiveSubcategory
attribute [cite HTT "5.2.7.9"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory
