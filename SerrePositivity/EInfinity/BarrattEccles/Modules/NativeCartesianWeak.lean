module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.Modules.LocalizationArrowCoefficients
public import SerrePositivity.EInfinity.Modules.LocalizationStrictWeak
public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRawCartesian

/-!
# 同じ BE 全加群族の標準 lift の実局所化辺

概要：HA §4.2.3 の同じ通常の標準 lift を実際の局所化の辺へ送る。
方針：指定生成射を使い、元の弱 lift 条件と射影の係数作用を保持する。
規約：native な Cartesian・cocartesian 性の証明は別に必要。
使われ方：M10 の同じ底の弱同値に沿う lift の反転。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：同じ全加群対象の元の局所化頂点（HTT Definition 1.1.5.5）。
方針：元の対象を同じ Hom 持ち上げと標準頂点同値に渡す。
規約：対象を選び直さない。使われ方：標準 lift の二端点。 -/
def moduleTotalVertex (M : strictRawModuleTotal A) : (moduleTotalInfinity A) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexEquiv (strictRawModuleTotalRelative A)
    ((ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleTotal A)).obj M)

/-- 概要：同じ標準 lift の実局所化辺（HTT Definition 1.1.5.5）。
方針：元の同じ二成分の射を指定生成辺へ送る。
規約：元の制限加群と対象を保つ。使われ方：弱 lift の反転と射影比較。 -/
def moduleCartesianLiftEdge {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    SSet.Edge (moduleTotalVertex A
      ((strictRawModuleFiberInclusion A X).obj ((strictRawModuleRestrict f).obj M)))
      (moduleTotalVertex A ((strictRawModuleFiberInclusion A Y).obj M)) :=
  coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom (strictRawModuleTotalRelative A)
    ((ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleTotal A)).map
      (strictRawModuleCartesianLift A f M)))

/-- 概要：底が準同型の同じ標準 lift の実辺は可逆（HTT §1.2.4）。
方針：元の全圏の弱射条件と、指定生成辺の反転の法則を使う。
規約：同じ実一単体。使われ方：弱底変更の native な反転。 -/
lemma moduleCartesianLiftEdge_invertible {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsInvertibleEdge (moduleCartesianLiftEdge A f M).toTruncated :=
  localizationStrictEdge_invertible_of_weak (strictRawModuleTotalRelative A) _
    (strictRawModuleCartesianLift_weak A f hf M)

/-- 概要：同じ標準 lift の射影は元の底の射の置換後の指定辺（HTT Definition 1.1.5.5）。
方針：元の係数作用の指定辺の保存と同じ底の成分を使う。
規約：全単体写像の一単体での等式。使われ方：指定された底上の lift の比較。 -/
lemma moduleCartesianLiftEdge_projection {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    ((moduleCartesianLiftEdge A f M).map (moduleTotalProjection A)).edge =
      (coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
        ((algebraToCofibrantDKRelative A).functor.map
          ((ULiftHom.up.{u,u+1,u+1} (C := (operad A).Algebra)).map f)))).edge := by
  exact localizationStrictEdge_coefficient
    (strictRawModuleTotalProjectionRelative A ≫ algebraToCofibrantDKRelative A)
    ((ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleTotal A)).map
      (strictRawModuleCartesianLift A f M))

attribute [cite HTT "1.1.5.5" (partial := component)
  "同じ BE 全加群の対象・標準 lift を、既存の nerve の指定頂点・辺へ移す部分。"]
  moduleTotalVertex moduleCartesianLiftEdge moduleCartesianLiftEdge_projection
attribute [cite HTT "1.2.4" (partial := component)
  "元の全圏の弱標準 lift に限り、その同じ実局所化辺の可逆性を示す。"]
  moduleCartesianLiftEdge_invertible

end SerrePositivity.EInfinity.BarrattEccles
