module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits

/-!
概要：一脚が Kan fibration の Kan 複体の引き戻しを 𝒮 の極限錐として公開する。
方針：台の引き戻し錐を束縛し、内部 Hom の極限保存と fibration 性の保存を検証する。
規約：左脚にのみ fibration 性を要求し、F1 の既存の空間値図式を使う。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB）、γ3c と F2 の引き戻し。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

variable {E B D : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (p : E ⟶ B) (q : D ⟶ B)

/-- 概要：二つの Kan 複体の射から小さい cospan の図式を作る。
方針：通常の cospan を AsSmall の添字に持ち上げる。
規約：左脚は p、右脚は q。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の strict な図式の ∞ 表示への入力。 -/
def kanPullbackDiagram : AsSmall.{u} WalkingCospan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  AsSmall.down ⋙ cospan p q

/-- 概要：Kan 複体の cospan の台の標準引き戻し錐。
方針：単体集合の標準引き戻し錐を持ち上げた添字へ制限する。
規約：錐の頂点は台の単体集合の pullback p q。
使われ方：HTT 4.2.4.1 の引き戻しの Hom 条件を検証する台の錐。 -/
noncomputable def kanPullbackUnderlyingCone : Cone (kanPullbackDiagram p q ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :=
  (Cone.postcompose (Functor.isoWhiskerLeft
    (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)
    (cospanCompIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget p q)).inv).obj
      ((pullback.cone (show E.obj ⟶ B.obj from p) (show D.obj ⟶ B.obj from q)).whisker
        (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan))

variable [Fibration (show E.obj ⟶ B.obj from p)]

/-- 概要：一脚 fibration の引き戻しの頂点を束縛した Kan 複体の錐。
方針：台の引き戻しの Kan 性で標準錐を束縛する。
規約：右脚 q の fibration 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の実際の strict な引き戻し錐。 -/
noncomputable def kanPullbackCone : Cone (kanPullbackDiagram p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying _ (kanPullbackUnderlyingCone p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pullback_kanComplex_of_fibration (show E.obj ⟶ B.obj from p) (show D.obj ⟶ B.obj from q))

/-- 概要：束縛した引き戻し錐の台の頂点は実際の単体集合の引き戻し。
方針：束縛した頂点の定義を計算する。
規約：対象の厳密な等号。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の 𝒮 の極限対象の明示。 -/
lemma kanPullbackCone_obj : (kanPullbackCone p q).pt.obj =
    pullback (show E.obj ⟶ B.obj from p) (show D.obj ⟶ B.obj from q) := rfl

/-- 概要：束縛した引き戻し錐は忘却後に標準の極限の普遍性を持つ。
方針：標準引き戻しの極限性を AsSmall の圏同値で移し、束縛して忘却する。
規約：台の引き戻しの実際の普遍性を使う。
使われ方：HTT 4.2.4.1 の全 Hom の極限条件の検証。 -/
noncomputable def kanPullbackCone_forget_isLimit :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (kanPullbackCone p q)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying_forget_isLimit
  apply (IsLimit.postcomposeInvEquiv
    (Functor.isoWhiskerLeft
      (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)
      (cospanCompIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget p q)) _).symm.toFun
  exact (pullback.isLimit (show E.obj ⟶ B.obj from p)
    (show D.obj ⟶ B.obj from q)).whiskerEquivalence
      (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm

/-- 概要：束縛した引き戻し錐は Kan 複体の通常の圏でも極限錐。
方針：忘却した錐の普遍性を Kan 複体の射へ戻す。
規約：左脚の台の fibration 性のみを仮定する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の strict な引き戻しの実際の対象。 -/
noncomputable def kanPullbackCone_isLimit : IsLimit (kanPullbackCone p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectCone_isLimit_of_forget _ (kanPullbackCone_forget_isLimit p q)

/-- 概要：𝒮 の既存の cospan の図式上の実際の引き戻し錐。
方針：Kan 複体の錐を coherent nerve に写し、F1 の空間値図式へ同定する。
規約：頂点の台は単体集合の pullback p q。
使われ方：HTT 4.2.4.1 の双対、γ3c と F2 の一脚 fibration の引き戻し。 -/
noncomputable def spacePullbackCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (kanPullbackDiagram p q)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (kanPullbackCone p q)).cast
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram (kanPullbackDiagram p q))

/-- 概要：Kan 複体の一脚 fibration の実際の引き戻しは 𝒮 の極限錐となる。
方針：内部 Hom による極限と fibration の保存を検証して cospan の移送定理を適用する。
規約：Hom 条件や追加の比較同値を仮定せず、左脚 p の fibration 性だけを要求する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB）、γ3c の具体的な引き戻し。 -/
lemma spacePullbackCone_isLimitCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (spacePullbackCone p q) := by
  have : ∀ X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (kanPullbackDiagram p q) X).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun X ↦ by
    change Fibration
      (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op X)).map p)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHom_map_fibration X p
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (kanPullbackCone p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget _ (kanPullbackCone_forget_isLimit p q))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
