module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductRealizationColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.LocalLeftKanColimitPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFilteredGeometricDetection
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction

/-!
概要：小余積と幾何学的実現の保存から全小余極限保存を導く。
方針：全単体の bar 展開の局所小余積と実現を保存し、局所化制限で元へ戻す。
規約：元の任意の小さい単体集合形状と指定全余錐を扱う。
使われ方：P_Σ 上の全余極限保存判定の一般段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：元の小さい離散図式の指定余極限を保つ条件。
方針：全小離散形状と全余錐像を量化する。
規約：空の小余積を含む。
使われ方：全小余極限保存の一般判定。 -/
def PreservesSmallCoproducts {X Y : SSet.{u + 1}} (U : X ⟶ Y) : Prop :=
  ∀ (I : Type u) (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X)
    (c : JoinCocone p), IsColimitCone c → IsColimitCone (mapJoinCocone U c)

/-- 概要：小余積を保つ関手は要素圏の次数射影の局所左 Kan 余極限を保つ。
方針：同じ cofinal な離散ファイバーに制限して保存を使い、元へ反映する。
規約：元の局所余錐を保持する。
使われ方：bar の各次数の小余積保存。 -/
lemma elementsCoproduct_leftKan_preservesColimit
    {I : Type u} [Category.{u} I] (Z : I ⥤ Type u)
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (U : X ⟶ Y) (hU : PreservesSmallCoproducts U)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Z.Elements) ⟶ X)
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌)
    (c : JoinCocone (leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Z))) F v))
    (hc : IsColimitCone c) : IsColimitCone (mapJoinCocone U c) := by
  rcases v with ⟨v⟩
  obtain ⟨i, rfl⟩ := nerveEquiv.symm.surjective v
  let a := elementsCoproductKanComparison Z i
  have ha := elementsCoproductKanComparison_isRightCofinal Z i
  apply (isColimitCone_iff_restrict_rightCofinal a ha (mapJoinCocone U c)).mpr
  exact hU _ _ (c.restrict a) ((isColimitCone_iff_restrict_rightCofinal a ha c).mp hc)

/-- 概要：小余積と幾何学的実現を保つ関手は全小余極限を保つ。
方針：全単体展開の局所小余積と実現に保存を使い、両標的で局所化制限を反映する。
規約：始域には小余積の存在だけを入力し、元の任意の指定余錐について結論する。
使われ方：有限余積と sifted 保存による全余極限保存判定の後半。 -/
lemma preservesSmallColimits_of_coproducts_geometricRealizations
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hX : HasSmallCoproducts X) (U : X ⟶ Y)
    (hcop : PreservesSmallCoproducts U) (hgeom : PreservesSmallGeometricRealizations U) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits U := by
  intro K F c hc
  let Z := simplicialBarSimplexFamily K
  let j := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap K)
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso (simplicialBarIndexNerveIso K)
  have hjX : IsFullyFaithful ((pre j).app X) := localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} K) X
  have hjY : IsFullyFaithful ((pre j).app Y) := localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} K) Y
  have heX := ((isPrecompositionEquivalence_of_iso e) X).choose.isFullyFaithful
  have heY := ((isPrecompositionEquivalence_of_iso e) Y).choose.isFullyFaithful
  have hcj := (isColimitCone_iff_restrict_of_fullyFaithful_pre j hjX c).mp hc
  have hce := (isColimitCone_iff_restrict_of_fullyFaithful_pre e.hom heX (c.restrict j)).mp hcj
  have hbar := colimitPreservation_of_localLeftKan
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Z)))
    (e.hom ≫ (j ≫ F)) U (elementsCoproduct_leftKanDiagram_hasColimit Z hX _)
    (elementsCoproduct_leftKan_preservesColimit Z U hcop _) hgeom
    ((c.restrict j).restrict e.hom) hce
  apply (isColimitCone_iff_restrict_of_fullyFaithful_pre j hjY (mapJoinCocone U c)).mpr
  apply (isColimitCone_iff_restrict_of_fullyFaithful_pre e.hom heY
    ((mapJoinCocone U c).restrict j)).mpr
  exact hbar

end SerrePositivity.InfinityCategories.F2.Presentable
