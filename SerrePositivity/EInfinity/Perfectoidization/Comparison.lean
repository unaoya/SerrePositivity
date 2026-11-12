module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgDiscreteUnderRecognition
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedFreeForget
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
# BS 界面の CAlg_R と D(R) の比較

概要：実 U・離散埋め込み・任意 coherent 極限保存を BS の添字圏で使う。
方針：既存の全関手比較と全整数次数のホモロジー比較を特殊化する。
規約：文献入力の存在宣言は import せず、通常の非完備代数も始域に含める。
使われ方：CAlg_R 上の界面から既存 G1 の D(R) 版を導く。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Perfectoidization
open CategoryTheory CategoryTheory.Limits SSet MonoidalCategory MonoidalClosed
open SerrePositivity.InfinityCategories
open SerrePositivity.BhattScholze.PerfectoidizationInterface
open BarrattEccles
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 概要：既存 G1 と同じ通常代数の CAlg_R 埋め込み。
方針：完成済みの Under 版を使う。規約：同じ宇宙と R 作用。
使われ方：界面の単位の始域。 -/
abbrev algebraEmbedding : algebraNerve R ⟶ CAlg_R R := discreteCAlgUnderEmbedding R

/-- 概要：通常代数の埋め込みの全関手比較。
方針：実 U の比較を代入する。規約：元の J を保持。
使われ方：単位と標的図式の輸送。 -/
def algebraEmbeddingForgetIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (algebraEmbedding R ≫ cAlgForgetDerived R) (J R) :=
  discreteCAlgUnderEmbedding_forgetIso R

/-- 概要：CAlg_R 内の離散対象。
方針：通常の Under 入力の本質像を使う。規約：全頂点同型を要求。
使われ方：BS の離散時の普遍性と整代数の欄。 -/
def IsDiscrete (x : (CAlg_R R) _⦋0⦌) : Prop :=
  ∃ S : A_R R, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x ((algebraEmbedding R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)))

/-- 概要：BS の離散性と CAlg_R の通常代数の本質像の一致。
方針：同じ U の全次数比較を代入する。規約：零次以外の全整数次数。
使われ方：universal と integral の述べ直し。 -/
lemma disc_forget_iff (x : (CAlg_R R) _⦋0⦌) :
    Disc R ((cAlgForgetDerived R).app _ x) ↔ IsDiscrete R x := by
  unfold IsDiscrete
  rw [← cAlgUnderlyingDisc_iff_discreteUnder R x]
  constructor
  · intro h i hi
    exact (h i hi).of_iso
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso R i _ ) ≪≫ (HIso R i _).symm)
  · intro h i hi
    exact (h i hi).of_iso
      ((HIso R i _) ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso R i _).symm)

/-- 概要：元の CAlg_R 単位を J 始域の実ホモトピーへ移す。
方針：全関手比較の逆と U 像を合成して代表を選ぶ。
規約：単位の二胞体の類を変更しない。
使われ方：既存 H0RingData と指定された BS 錐。 -/
def underlyingUnit {P : algebraNerve R ⟶ CAlg_R R}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (algebraEmbedding R) P) :
    NatInfinity R (J R) (P ≫ cAlgForgetDerived R) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy ((algebraEmbeddingForgetIso R).inv ≫
    (SSet.mapHomotopyCategory ((ihom (algebraNerve R)).map (cAlgForgetDerived R))).map η)

/-- 概要：底の実単位の二胞体の回収。
方針：ホモトピー代表の仕様を使う。規約：元の単位の U 像との合成。
使われ方：代表の選択によって単位を変えていないことの確認。 -/
lemma underlyingUnit_hom {P : algebraNerve R ⟶ CAlg_R R}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (algebraEmbedding R) P) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (underlyingUnit R η)) =
      (algebraEmbeddingForgetIso R).inv ≫
        (SSet.mapHomotopyCategory ((ihom (algebraNerve R)).map (cAlgForgetDerived R))).map η :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom _

/-- 概要：同じ perfectoid 標的の CAlg_R 図式。
方針：同じ通常代数関手を離散埋め込みへ送る。規約：添字の向きを変えない。
使われ方：BS の指定極限。 -/
def targetCAlgDiagram (p : ℕ) [Fact p.Prime] (S : A_R R) :
    perfectoidTargetNerve p S.right ⟶ CAlg_R R :=
  nerveMap (targetAlgebra R p S) ≫ algebraEmbedding R

/-- 概要：同じ perfectoid 標的図式の全関手比較。
方針：離散比較を標的関手で前合成する。規約：全単体を保持。
使われ方：指定錐の比較の境界条件。 -/
def targetCAlgDiagramForgetIso (p : ℕ) [Fact p.Prime] (S : A_R R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (targetCAlgDiagram R p S ≫ cAlgForgetDerived R) (targetDiagram R p S) :=
  (algebraEmbeddingForgetIso R).precomp (nerveMap (targetAlgebra R p S))

/-- 概要：実 U は元の正方形の引き戻し性を保存する。
方針：対応する指定 coherent 錐へ任意極限保存を適用する。
規約：全正方形を同じ U で後合成。使われ方：BS excision の D(R) 版。 -/
lemma forget_pullback {F : Δ[1] ⊗ Δ[1] ⟶ CAlg_R R} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ cAlgForgetDerived R) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_of_diagram_eq (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, Category.assoc])
    (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone, Category.assoc])).mp
      (cAlgForgetDerived_mapJoinCone_isLimit R (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F) hF)

end SerrePositivity.EInfinity.Perfectoidization
