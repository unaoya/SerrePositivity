module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpanPointHomCospan

/-!
概要：二辺の span の余錐空間を、各頂点からの点 Hom の cospan の end と比較する。
方針：二辺への制限の厳密な引き戻しと、終点制限の切断の成分ごとの同値を使う。
規約：値域は任意の quasicategory。通常の span の nerve への表示変更は別に扱う。
使われ方：部分余極限対象の native な span の余錐空間を共通の Hom の end へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X] (p : (horn 2 0 : SSet.{u}) ⟶ X) (y : X _⦋0⦌)

/-- span の点 Hom の図式は成分ごとに Kan。 -/
instance spanPointHomCospan_obj_kanComplex (k : AsSmall.{u} WalkingCospan) :
    KanComplex ((spanPointHomCospan p y).obj k) := by
  rcases k with ⟨k⟩
  cases k with
  | none => exact coconeMappingSpace_kanComplex _ _
  | some k => cases k <;> exact coconeMappingSpace_kanComplex _ _

/-- span の辺全体の余錐空間の図式も成分ごとに Kan。 -/
instance spanEdgeCoconeCospan_obj_kanComplex (k : AsSmall.{u} WalkingCospan) :
    KanComplex ((spanEdgeCoconeCospan p y).obj k) := by
  rcases k with ⟨k⟩
  cases k with
  | none => exact coconeMappingSpace_kanComplex _ _
  | some k => cases k <;> exact coconeMappingSpace_kanComplex _ _

/-- 点 Hom の end から、辺全体の余錐空間の end への実際の誘導射。 -/
def spanPointHomToEdgeEnd :
    weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan)) (spanPointHomCospan p y) ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (spanEdgeCoconeCospan p y) :=
  weightedSectionsMap _ (spanPointHomToEdgeCocones p y)

/-- 両辺の終点制限の切断は end でもホモトピー同値を与える。 -/
lemma spanPointHomToEdgeEnd_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (spanPointHomToEdgeEnd p y) :=
  bousfieldKanMap_homotopyEquivalence _ (spanPointHomToEdgeCocones_app_homotopyEquivalence p y)

/-- span の元の余錐空間から二辺の余錐空間の end への標準比較。 -/
def spanCoconeToEdgeEnd :
    coconeMappingSpace p y ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (spanEdgeCoconeCospan p y) :=
  bousfieldKanConeComparison (coconeMappingShapeCospanCone horn₂₀.isPushout p y)

/-- span の元の余錐空間は、二辺の余錐空間の end と実際の比較射でホモトピー同値。 -/
lemma spanCoconeToEdgeEnd_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (spanCoconeToEdgeEnd p y) := by
  have : Fibration ((spanEdgeCoconeCospan p y).map (AsSmall.up.map WalkingCospan.Hom.inl)) :=
    coconeMappingShapePushout_right_fibration horn₂₀.isPushout p y
  exact bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
    (spanEdgeCoconeCospan p y) (coconeMappingShapeCospanCone horn₂₀.isPushout p y)
    (coconeMappingShapeCospanCone_isLimit horn₂₀.isPushout p y)

/-- 辺全体の余錐空間の end から点 Hom の end へのホモトピー逆を一つ選ぶ。 -/
def spanEdgeEndToPointHomEnd :
    weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan)) (spanEdgeCoconeCospan p y) ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan)) (spanPointHomCospan p y) :=
  (spanPointHomToEdgeEnd_homotopyEquivalence p y).choose

/-- 選んだ逆も、点 Hom の end への実際のホモトピー同値。 -/
lemma spanEdgeEndToPointHomEnd_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (spanEdgeEndToPointHomEnd p y) := by
  let h := spanPointHomToEdgeEnd_homotopyEquivalence p y
  exact ⟨spanPointHomToEdgeEnd p y, h.choose_spec.2, h.choose_spec.1⟩

/-- span の余錐空間から、その三頂点の点 Hom の cospan の end への実際の比較射。 -/
def spanCoconeToPointHomEnd :
    coconeMappingSpace p y ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan)) (spanPointHomCospan p y) :=
  spanCoconeToEdgeEnd p y ≫ spanEdgeEndToPointHomEnd p y

/-- span の余錐空間と三頂点の点 Hom の end は、実際の比較射でホモトピー同値。 -/
lemma spanCoconeToPointHomEnd_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (spanCoconeToPointHomEnd p y) := by
  have : KanComplex (coconeMappingSpace p y) := coconeMappingSpace_kanComplex _ _
  have : KanComplex (bousfieldKanHolim (spanEdgeCoconeCospan p y)) := bousfieldKanHolim_kanComplex _
  exact (spanCoconeToEdgeEnd_homotopyEquivalence p y).comp
    (spanEdgeEndToPointHomEnd_homotopyEquivalence p y)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
