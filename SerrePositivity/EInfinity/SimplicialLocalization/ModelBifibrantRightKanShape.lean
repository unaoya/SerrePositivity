module

public import SerrePositivity.InfinityCategories.ModelBridge.ModelBifibrantFrame
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelCofibrantRightKanShape
public import SerrePositivity.EInfinity.SimplicialLocalization.WeakNerveInverts
public import SerrePositivity.EInfinity.FrameHom.FrameRightKan
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.Terminal

/-!
概要：任意モデル圏の元の bifibrant frame から実 right Kan 形状への次数比較を作る。
方針：元の augmentation の全成分を同時に反転する実関手同型を使う。
規約：同じ局所化頂点と全次数の射影を保持し、余終性は後続で証明する。
使われ方：代数版の三つの局所化判定入力の一般化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Limits HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
open FrameHom.FrameArrows
open scoped Simplicial

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

/-- 概要：元の bifibrant 対象の同じ Kan hammock 局所化頂点。
方針：元の包含頂点を元の局所化写像で送る。
規約：代表頂点を変更しない。使われ方：実 right Kan 形状の基点。 -/
def modelBifibrantHammockVertex : (kanHammockNerve (modelBifibrantRelativeCategory C)) _⦋0⦌ :=
  (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)).app (op ⦋0⦌)
    (nerveVertex (modelBifibrantObject C X))

/-- 概要：元の augmentation の全成分は同じ hammock 像で可逆。
方針：元の弱同値の辺反転を各成分に適用する。
規約：元の単体的辺自身を保持。使われ方：全次数の実 coslice 実現。 -/
lemma modelBifibrantFrameAugmentation_invertible (n : AsSmall.{max u v} SimplexCategory) :
    IsInvertibleEdge ((nerve.edgeMk ((modelBifibrantDKFrameAugmentation X q).app n)).map
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))).toTruncated :=
  weakNerveEdges_inverts_arrows (modelBifibrantRelativeCategory C) _
    (hammockLocalizationNerveMap_inverts (modelBifibrantRelativeCategory C)) _
    (modelBifibrantDKFrameAugmentation_weak X q n)

/-- 概要：同じ frame の全次数から実 right Kan 形状への実比較。
方針：同じ augmentation の全関手同型から元の coslice を実現する。
規約：同じ qX と全次数を保持。使われ方：局所極限を移すための次数比較。 -/
def modelBifibrantFrameRightKanMap : nerve (AsSmall.{max u v} SimplexCategory) ⟶
    rightKanShape (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (modelBifibrantHammockVertex X) :=
  frameRightKanMap (modelBifibrantDKFrame X q) (modelBifibrantDKFrameAugmentation X q)
    (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
    (modelBifibrantFrameAugmentation_invertible X q)

/-- 概要：元の次数比較の始域射影は同じ frame の nerve。
方針：同じ pullback の第二射影を読む。
規約：実射の厳密な等式。使われ方：全局所図式の制限の照合。 -/
lemma modelBifibrantFrameRightKanMap_projection : modelBifibrantFrameRightKanMap X q ≫
    rightKanProjection (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (modelBifibrantHammockVertex X) = nerveMap (modelBifibrantDKFrame X q) :=
  frameRightKanMap_projection _ _ _ _

/-- 概要：同じ次数比較に沿う局所図式の制限は元の frame 図式。
方針：同じ次数比較の射影等式を使う。
規約：全対象関手 F で成立。使われ方：実 right Kan 局所極限への移送。 -/
lemma modelBifibrantFrameRightKanMap_diagram {E : SSet.{max u v}}
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E) :
    modelBifibrantFrameRightKanMap X q ≫ rightKanDiagram
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) F
      (modelBifibrantHammockVertex X) = nerveMap (modelBifibrantDKFrame X q) ≫ F :=
  frameRightKanMap_diagram _ _ _ _ F

/-- 概要：元の弱同値を反転する全関手は同じ frame 図式の実極限を持つ。
方針：可逆な全 augmentation と元の次数圏の弱可縮性を使う。
規約：点ごとの関手同型で全自然性を代用しない。使われ方：right Kan 局所極限の入力。 -/
lemma modelBifibrantFrame_hasLimit {E : SSet.{max u v}} [SSet.Quasicategory E]
    (F : nerve (modelBifibrantRelativeCategory C).category ⟶ E)
    (hF : InvertsEdges F (weakNerveEdges (modelBifibrantRelativeCategory C))) :
    HasLimit (nerveMap (modelBifibrantDKFrame X q) ≫ F) := by
  apply (target_hasLimit_iff (modelBifibrantDKFrame X q) F).mp
  apply target_hasLimit_of_inverting_augmentation
    (modelBifibrantDKFrame X q) (modelBifibrantDKFrameAugmentation X q) F
  · intro n
    exact weakNerveEdges_inverts_arrows _ F hF _
      (modelBifibrantDKFrameAugmentation_weak X q n)
  · exact modelFrameIndex_weaklyContractible

end SerrePositivity.EInfinity.SimplicialLocalization
