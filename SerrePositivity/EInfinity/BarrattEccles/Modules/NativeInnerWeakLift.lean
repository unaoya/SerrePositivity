module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.TotalInnerReplacement
public import SerrePositivity.EInfinity.BarrattEccles.Modules.NativeCartesianWeak
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian

/-!
# 同じ弱底変更の実 lift の native な相対性

概要：HTT Proposition 2.4.1.5 の同値辺の相対性を同じ BE の弱 lift に適用する。
方針：元の弱 lift の同じ実辺を inner anodyne 置換へ移し、可逆性を使う。
規約：底の指定辺と全単体の射影を保持する。一般の底の射の lift は別に必要。
使われ方：M10 の弱底変更の実 Cartesian・cocartesian 辺。
Kerodon Proposition 5.1.1.9（Tag 01TB）の同じ相対外ホーン充填を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.EInfinity _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：同じ元の標準 lift を置換後の全圏へ移す（HTT §2.4.1）。
方針：元の実一単体を同じ包含で写す。
規約：元の両端点の像。使われ方：実射影に関する弱 lift の相対性。 -/
def moduleInnerCartesianLiftEdge {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    SSet.Edge ((moduleTotalInnerInclusion A).app (Opposite.op ⦋0⦌)
      (moduleTotalVertex A ((strictRawModuleFiberInclusion A X).obj
        ((strictRawModuleRestrict f).obj M))))
      ((moduleTotalInnerInclusion A).app (Opposite.op ⦋0⦌)
        (moduleTotalVertex A ((strictRawModuleFiberInclusion A Y).obj M))) :=
  (moduleCartesianLiftEdge A f M).map (moduleTotalInnerInclusion A)

/-- 概要：同じ弱 lift の実辺は置換後も可逆（HTT §1.2.4）。
方針：同じ実辺の可逆性を同じ包含で移す。
規約：別の辺を選ばない。使われ方：相対外ホーン充填の入力。 -/
lemma moduleInnerCartesianLiftEdge_invertible {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsomorphismsAndIsofibrations.IsInvertibleEdge (moduleInnerCartesianLiftEdge A f M).toTruncated :=
  (moduleCartesianLiftEdge_invertible A f hf M).map (moduleTotalInnerInclusion A)

/-- 概要：同じ置換後の lift は元の底の指定辺に射影する（HTT §2.4.1）。
方針：同じ包含と射影の厳密な合成式を一単体で評価する。
規約：底の元の射と置換を保持する。使われ方：同じ底上の lift の照合。 -/
lemma moduleInnerCartesianLiftEdge_projection {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    ((moduleInnerCartesianLiftEdge A f M).map (moduleTotalInnerProjection A)).edge =
      (coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
        ((algebraToCofibrantDKRelative A).functor.map
          ((ULiftHom.up.{u,u+1,u+1} (C := (operad A).Algebra)).map f)))).edge := by
  change (moduleTotalInnerInclusion A ≫ moduleTotalInnerProjection A).app (Opposite.op ⦋1⦌)
    (moduleCartesianLiftEdge A f M).edge = _
  rw [moduleTotalInnerInclusion_projection]
  exact moduleCartesianLiftEdge_projection A f M

/-- 概要：同じ弱底変更の標準 lift は native に Cartesian（HTT Proposition 2.4.1.5）。
方針：証明済みの inner fibration と同じ辺の可逆性から全相対外ホーンを充填する。
規約：モデル圏の仮定や Cartesian 性の仮定を加えない。使われ方：M10 の弱底変更。 -/
lemma moduleInnerCartesianLiftEdge_cartesian {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsCartesianEdge (moduleTotalInnerProjection A) (moduleInnerCartesianLiftEdge A f M).edge :=
  isCartesianEdge_of_isInvertibleEdge (moduleTotalInnerProjection A) _
    (moduleInnerCartesianLiftEdge_invertible A f hf M)

/-- 概要：同じ弱底変更の標準 lift は native に cocartesian（HTT Proposition 2.4.1.5）。
方針：同じ可逆辺に初端の相対外ホーンの充填を適用する。
規約：底が弱同値の同じ lift に限る。使われ方：M10 の同じ弱輸送の反転。 -/
lemma moduleInnerCartesianLiftEdge_cocartesian {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsCocartesianEdge (moduleTotalInnerProjection A) (moduleInnerCartesianLiftEdge A f M).edge :=
  isCocartesianEdge_of_isInvertibleEdge (moduleTotalInnerProjection A) _
    (moduleInnerCartesianLiftEdge_invertible A f hf M)

attribute [cite HTT "1.2.4" (partial := component)
  "元の弱標準 lift の同じ実辺を包含で移した可逆性だけを照合する。"]
  moduleInnerCartesianLiftEdge_invertible
attribute [cite HTT "2.4.1.5" (partial := component)
  "同じ BE の弱底変更の指定 lift に限り、構成した inner fibration に関する相対性を示す。"]
  moduleInnerCartesianLiftEdge moduleInnerCartesianLiftEdge_projection
  moduleInnerCartesianLiftEdge_cartesian moduleInnerCartesianLiftEdge_cocartesian

end SerrePositivity.EInfinity.BarrattEccles
