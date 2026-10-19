module

public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyCospanConeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentHomNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeMappingShapePushout

/-!
概要：元の coherent 図式の余錐空間と、部分余極限頂点の Hom の cospan の end を共通模型で比較する。
方針：二枝の Hom 比較の単体的ホモトピーを path 置換への自然変換へ束ね、元の引き戻し錐を使う。
規約：共通部分・両側の指定余錐は余極限。右境界の単射性は比較の同値性にのみ要求する。
使われ方：部分余極限対象の span の余錐空間と、貼り合わせた元の余錐の普遍性の接続。
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
variable {A B C D X : SSet.{u}} [Quasicategory X] {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ X) (y : X _⦋0⦌)

/-- 元の固定終点余錐空間を頂点とする、二枝の制限の cospan の厳密な錐。 -/
def coconeMappingShapeCospanCone :
    Cone (AsSmall.down ⋙ cospan
      (normalizedCoconeRestrictionFiber (j ≫ p) g (coconePushoutBoundary_eq hp p) y)
      (cosliceRestrictionFiberMap (i ≫ p) f y)) :=
  (PullbackCone.mk (cosliceRestrictionFiberMap p j y) (cosliceRestrictionFiberMap p i y)
    (coconeMappingShapePushout_isPullback hp p y).w.symm).whisker
      (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)

/-- 元の図式の余錐空間を頂点とする錐は、実際の厳密な極限錐。 -/
def coconeMappingShapeCospanCone_isLimit : IsLimit (coconeMappingShapeCospanCone hp p y) :=
  (coconeMappingShapePushout_isPullback hp p y).flip.isLimit.whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm

variable (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB)
  (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC)

/-- 部分余極限の実際の比較辺の前合成を構造射とする左 Hom の cospan。 -/
def partialColimitHomCospan : AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  AsSmall.down ⋙ cospan
    (colimitAttachmentHomPrecomposition c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC y)
    (colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y)

/-- 元の図式の余錐空間と Hom の end が共に写る、path 置換した Hom 図式の end。 -/
def partialColimitHomPathEnd : SSet.{u} :=
  weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
    (cospanPathDiagram
      (colimitAttachmentHomPrecomposition c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC y)
      (colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y))

/-- 元の余錐空間から Hom の共通 end への実際の比較射。 -/
def partialColimitCoconeHomEndComparison :
    coconeMappingSpace p y ⟶ partialColimitHomPathEnd hp p y c hc dB dC := by
  have : KanComplex (vertexFiber (sliceUnderProjection (i ≫ p)) y) :=
    coconeMappingSpace_kanComplex _ _
  have : KanComplex (vertexFiber (sliceUnderProjection (j ≫ p)) y) :=
    coconeMappingSpace_kanComplex _ _
  have : KanComplex (vertexFiber (sliceUnderProjection (f ≫ (i ≫ p))) y) :=
    coconeMappingSpace_kanComplex _ _
  let HR := (coconeMappingSpaceHomComparison_restrict_square c hc g (j ≫ p)
    (coconePushoutBoundary_eq hp p) dC hC y).some
  have HL : Nonempty (SSet.Homotopy
      (cosliceRestrictionFiberMap (i ≫ p) f y ≫ coconeMappingSpaceHomComparison c hc y)
      (coconeMappingSpaceHomComparison dB hB y ≫
        colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y)) := by
    simpa only [normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id] using
      coconeMappingSpaceHomComparison_restrict_square c hc f (i ≫ p) rfl dB hB y
  exact homotopyCospanConeComparison _ _ _ _
    (coconeMappingSpaceHomComparison dC hC y) (coconeMappingSpaceHomComparison c hc y)
    (coconeMappingSpaceHomComparison dB hB y) HR HL.some (coconeMappingShapeCospanCone hp p y)

/-- 一脚が単射なら、元の図式の余錐空間から Hom の共通 end への比較はホモトピー同値。 -/
lemma partialColimitCoconeHomEndComparison_homotopyEquivalence [Mono g] :
    IsSimplicialHomotopyEquivalence
      (partialColimitCoconeHomEndComparison hp p y c hc dB hB dC hC) := by
  have : KanComplex (vertexFiber (sliceUnderProjection (i ≫ p)) y) :=
    coconeMappingSpace_kanComplex _ _
  have : KanComplex (vertexFiber (sliceUnderProjection (j ≫ p)) y) :=
    coconeMappingSpace_kanComplex _ _
  have : KanComplex (vertexFiber (sliceUnderProjection (f ≫ (i ≫ p))) y) :=
    coconeMappingSpace_kanComplex _ _
  have := coconeMappingShapePushout_right_fibration hp p y
  apply homotopyCospanConeComparison_homotopyEquivalence
  · exact coconeMappingShapeCospanCone_isLimit hp p y
  · exact coconeMappingSpaceHomComparison_homotopyEquivalence dC hC y
  · exact coconeMappingSpaceHomComparison_homotopyEquivalence c hc y
  · exact coconeMappingSpaceHomComparison_homotopyEquivalence dB hB y

/-- 部分余極限の Hom の cospan の end から、同じ共通模型への実際の射。 -/
def partialColimitHomEndToPathEnd :
    weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (partialColimitHomCospan hp p y c hc dB dC) ⟶
      partialColimitHomPathEnd hp p y c hc dB dC :=
  cospanPathSectionEnd _ _

/-- Hom の cospan の end も、共通模型と実際の比較射でホモトピー同値。 -/
lemma partialColimitHomEndToPathEnd_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (partialColimitHomEndToPathEnd hp p y c hc dB dC) :=
  cospanPathSectionEnd_homotopyEquivalence _ _

/-- 共通の path end は、実際の Kan 複体として利用できる。 -/
instance partialColimitHomPathEnd_kanComplex :
    KanComplex (partialColimitHomPathEnd hp p y c hc dB dC) :=
  bousfieldKanWeightedSections_kanComplex _

/-- 元の Hom の cospan も成分ごとに Kan。 -/
instance partialColimitHomCospan_obj_kanComplex (k : AsSmall.{u} WalkingCospan) :
    KanComplex ((partialColimitHomCospan hp p y c hc dB dC).obj k) :=
  inferInstanceAs (KanComplex ((AsSmall.down ⋙ cospan
    (colimitAttachmentHomPrecomposition c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC y)
    (colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y)).obj k))

/-- 共通の path 模型から元の Hom の end へのホモトピー逆を一つ選ぶ。 -/
def partialColimitHomEndRetraction :
    partialColimitHomPathEnd hp p y c hc dB dC ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (partialColimitHomCospan hp p y c hc dB dC) :=
  (partialColimitHomEndToPathEnd_homotopyEquivalence hp p y c hc dB dC).choose

/-- 選んだ逆も、元の end への実際の単体的ホモトピー同値。 -/
lemma partialColimitHomEndRetraction_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (partialColimitHomEndRetraction hp p y c hc dB dC) := by
  let h := partialColimitHomEndToPathEnd_homotopyEquivalence hp p y c hc dB dC
  exact ⟨partialColimitHomEndToPathEnd hp p y c hc dB dC, h.choose_spec.2, h.choose_spec.1⟩

/-- 元の余錐空間から、部分余極限頂点の Hom の end への実際の比較射。 -/
def partialColimitCoconeToHomEnd :
    coconeMappingSpace p y ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (partialColimitHomCospan hp p y c hc dB dC) :=
  partialColimitCoconeHomEndComparison hp p y c hc dB hB dC hC ≫
    partialColimitHomEndRetraction hp p y c hc dB dC

/-- 元の余錐空間と部分余極限頂点の Hom の end は、実際の比較射でホモトピー同値。 -/
lemma partialColimitCoconeToHomEnd_homotopyEquivalence [Mono g] :
    IsSimplicialHomotopyEquivalence (partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC) := by
  have : KanComplex (coconeMappingSpace p y) := coconeMappingSpace_kanComplex _ _
  exact (partialColimitCoconeHomEndComparison_homotopyEquivalence hp p y c hc dB hB dC hC).comp
    (partialColimitHomEndRetraction_homotopyEquivalence hp p y c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
