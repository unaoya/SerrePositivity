module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleLocalizationUniversal
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleSourceRestriction
public import SerrePositivity.KST.LocalizingInvariants.LocalizationFactorization

/-!
# 元の加群局所化から指定半自由模型への全比較

概要：M10/C02 の同じ通常源の関手を、証明済みの全標的普遍性で降下する。
方針：既存の localizationDescend と同じ全三角比較を使い、指定頂点・正則加群を回収する。
規約：HA §4.2.3、完全忠実性はここで主張しない。
使われ方：同じ U・単位・全制限を持つ fiber 同定への比較候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open FullFaithfulAndEssentiallySurjectiveFunctors
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：同じ通常加群 DK 局所化から指定半自由模型への全関手。
方針：同じ通常源の擬同型反転を、証明済み局所化普遍性へ渡す。
規約：HA §4.2.3、全単体を保持。使われ方：M10/C02 の fiber 比較。 -/
def strictRawModuleComparison (X : (operad A).Algebra) :
    localizationNerve (strictRawModuleRelativeCategory A X) ⟶ strictModuleInfinity A X :=
  SerrePositivity.KST.LocalizingInvariants.localizationDescend
    (localizationNerveSourceMap (strictRawModuleRelativeCategory A X))
    (weakNerveEdges (strictRawModuleRelativeCategory A X))
    (strictRawModuleLocalization_isLocalization A X) (strictRawModuleSource A X)
    (strictRawModuleSource_inverts A X)

/-- 概要：降下した同じ比較は元の全通常源と指定三角同型を持つ。
方針：同じ普遍性の選択に付随する全関手同型を回収する。
規約：HA §4.2.3、対象ごとの比較に弱めない。使われ方：U・単位・制限との照合。 -/
def strictRawModuleComparison_sourceIso (X : (operad A).Algebra) :
    FunctorIso
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫
        strictRawModuleComparison A X)
      (strictRawModuleSource A X) :=
  SerrePositivity.KST.LocalizingInvariants.localizationDescendIso
    (localizationNerveSourceMap (strictRawModuleRelativeCategory A X))
    (weakNerveEdges (strictRawModuleRelativeCategory A X))
    (strictRawModuleLocalization_isLocalization A X) (strictRawModuleSource A X)
    (strictRawModuleSource_inverts A X)

/-- 概要：同じ比較の標準頂点での値は指定された元の半自由分解。
方針：同じ通常源の指定頂点同型と三角比較の成分を貼る。
規約：HA §4.2.3、元の通常対象。使われ方：正則加群の値。 -/
def strictRawModuleComparison_vertexIso (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    VertexIso
      ((strictRawModuleComparison A X).app (Opposite.op ⦋0⦌)
        (localizationNerveVertexEquiv (strictRawModuleRelativeCategory A X)
          (show KanLocalizationCategory (strictRawModuleRelativeCategory A X) from M)))
      ((strictRawModuleSource A X).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ M)) :=
  ((localizationNerveSourceMap_vertexIso (strictRawModuleRelativeCategory A X) M).map
    (strictRawModuleComparison A X)).symm ≪≫
      (strictRawModuleComparison_sourceIso A X).app (ComposableArrows.mk₀ M)

/-- 概要：同じ降下比較は全ての半自由対象を同値まで覆う。
方針：元の通常源の本質的全射性に、同じ全三角の成分を貼る。
規約：HA §4.2.3、完全忠実性は別。使われ方：同じ fiber 比較の対象の側。 -/
lemma strictRawModuleComparison_essentiallySurjective (X : (operad A).Algebra) :
    IsEssentiallySurjective (strictRawModuleComparison A X) := by
  intro y
  obtain ⟨x, ⟨e⟩⟩ := strictRawModuleSource_essentiallySurjective A X y
  refine ⟨(localizationNerveSourceMap (strictRawModuleRelativeCategory A X)).app
    (Opposite.op ⦋0⦌) x, ⟨?_⟩⟩
  exact (strictRawModuleComparison_sourceIso A X).app x ≪≫ e

/-- 概要：元の正則加群の標準局所化頂点を指定単位へ比較する。
方針：同じ比較の頂点式と通常源の正則加群の式を合成する。
規約：HA §4.2.3、元の単位を保持。使われ方：C02 の指定単位の照合。 -/
def strictRawModuleComparison_regularIso (X : (operad A).Algebra) :
    VertexIso
      ((strictRawModuleComparison A X).app (Opposite.op ⦋0⦌)
        (localizationNerveVertexEquiv (strictRawModuleRelativeCategory A X)
          (show KanLocalizationCategory (strictRawModuleRelativeCategory A X) from
            (ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj
              (strictRawRegularObject A X).fiber)))
      (strictModuleUnit A X) := by
  have e := strictRawModuleComparison_vertexIso A X
    ((ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj
      (strictRawRegularObject A X).fiber)
  rw [strictRawModuleSource_regular A X] at e
  exact e

/-- 概要：同じ降下の全三角は同じ台の忘却と可換。
方針：指定三角比較を同じ U で後合成する。
規約：HA §4.2.1、全関手間の比較。使われ方：C02 の同じ台の比較。 -/
def strictRawModuleComparison_sourceUnderlyingIso (X : (operad A).Algebra) :
    FunctorIso
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫
        strictRawModuleComparison A X ≫ strictModuleUnderlying A X)
      (strictRawModuleSource A X ≫ strictModuleUnderlying A X) :=
  (strictRawModuleComparison_sourceIso A X).postcomp (strictModuleUnderlying A X)

end SerrePositivity.EInfinity.BarrattEccles
