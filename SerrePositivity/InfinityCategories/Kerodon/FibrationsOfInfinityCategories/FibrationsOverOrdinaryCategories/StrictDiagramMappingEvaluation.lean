module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictDiagramMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.F1ScaffoldUniversalScaffold

/-!
概要：strict な自然変換の空間全体を用いた simplicial replacement の評価。
方針：係数の自然変換の普遍評価と、simplicial replacement への追加パラメーターの移送を合成する。
規約：追加パラメーターは全次数で保持する。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、Corollary 5.6.0.6（Tag 028T）、相対写像空間の逆向きの比較の構成。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：strict な自然変換の空間全体の評価は係数図式間の通常の自然変換になる。
方針：対象ごとの内部 Hom の成分を uncurry し、単体の自然性条件を適用する。
規約：始域図式の全ての値に同じ変換の空間をテンソルする。
使われ方：Kerodon §5.3.1（Tag 035D）、パラメーター付きの係数の自然変換の評価。 -/
def strictDiagramMappingEvaluation {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    F ⋙ tensorRight (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) ⟶ G where
  app c := uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G c)
  naturality c d f := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, η⟩
    exact (η.property f n (𝟙 n) x).symm

/-- 概要：simplicial replacement の追加パラメーターを、係数図式への同じテンソル因子として移す。
方針：底の射列を保ち、係数単体とパラメーター単体を対にする。
規約：パラメーターの単体集合 T は任意。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、全変換の空間を保った scaffold の評価。 -/
def simplicialReplacementTensorMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (T : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⊗ T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement (F ⋙ tensorRight T) where
  app _ := ↾fun ⟨s, t⟩ ↦ ⟨s.1, lift s.2 (SSet.yonedaEquiv.symm t)⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨σ, τ⟩, t⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    change lift (stdSimplex.map α.unop ≫ τ ≫ F.map (σ.map (homOfLE _)))
      (SSet.yonedaEquiv.symm (T.map α t)) =
      stdSimplex.map α.unop ≫ lift τ (SSet.yonedaEquiv.symm t) ≫
        (F.map (σ.map (homOfLE _)) ▷ T)
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · exact (ConcreteCategory.congr_hom (NatTrans.congr_app
        (SSet.yonedaEquiv_symm_naturality_left α.unop t) d) x).symm

/-- 概要：パラメーターを係数へ移す射は、底では元の simplicial replacement の射影に一致する。
方針：底の射列の成分を計算する。
規約：パラメーターは第一射影で忘れる。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、scaffold の評価を相対 Hom へ入れる底の条件。 -/
lemma simplicialReplacementTensorMap_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (T : SSet.{u}) :
    simplicialReplacementTensorMap F T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (F ⋙ tensorRight T) =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F := rfl

/-- 概要：strict な自然変換の空間全体で、始域の simplicial replacement を標的の replacement へ評価する。
方針：変換のパラメーターを係数へ移し、係数の普遍評価を simplicial replacement に写す。
規約：底の nerve への射影を保つ。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、strict transport の写像空間の逆向きの比較。 -/
def strictDiagramMappingReplacementEvaluation {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement G :=
  simplicialReplacementTensorMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap (strictDiagramMappingEvaluation F G)

/-- 概要：replacement の全変換の評価の底は元の底の射影をパラメーターに関して一定にしたもの。
方針：係数の自然変換とパラメーター移送がともに底を保つことを使う。
規約：係数の二つの図式の底は同じ通常の圏 C。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、相対関手空間への評価の持ち上げ。 -/
lemma strictDiagramMappingReplacementEvaluation_projection
    {C : Type u} [Category.{u} C] (F G : C ⥤ SSet.{u}) :
    strictDiagramMappingReplacementEvaluation F G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection G =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F := by
  rw [strictDiagramMappingReplacementEvaluation, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap_projection, simplicialReplacementTensorMap_projection]

/-- 概要：strict な変換の空間から、始域の replacement から標的の left fibration への相対 Hom への評価射。
方針：標的の strict transport の replacement を universal scaffold で評価し、底上の族を相対 curry する。
規約：q の left fibration 性はこの射の定義には不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の写像空間比較の逆を構成する第一段階。 -/
def strictDiagramMappingScaffoldMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry
    (strictDiagramMappingReplacementEvaluation F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold q)
    (by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold_projection,
      strictDiagramMappingReplacementEvaluation_projection])

/-- 概要：相対射を strict transport の自然変換へ写して scaffold で評価すると、元の射の scaffold に沿う前合成になる。
方針：相対 Hom の包含と uncurry の後、各単体の二回の対角評価を比較する。
規約：p と q の充填性は不要で、底上の射として厳密に可換。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、Corollary 5.6.0.6（Tag 028T）、写像空間の逆向きの比較の片側の合成。 -/
lemma leftStrictTransportMappingSpaceMap_scaffold
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMappingSpaceMap p q ≫
        strictDiagramMappingScaffoldMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q (Over.homMk
        (U := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p)))
        (V := Over.mk p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold_projection p)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  apply uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
