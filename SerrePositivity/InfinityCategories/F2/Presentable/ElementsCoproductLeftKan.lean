module

public import SerrePositivity.InfinityCategories.F2.Presentable.ElementsDegreeFiber
public import SerrePositivity.InfinityCategories.F2.Presentable.CofinalColimitExistence
public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductRealizationConditions
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.F2.Idempotent.UniverseLeftKanShape
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCoconeColimit

/-!
概要：小余積を持つ標的への要素圏の次数射影に沿う全左 Kan 延長。
方針：各局所添字を同じ離散ファイバーへ cofinal に縮約する。
規約：標的に全小余極限や前層表示を仮定しない。
使われ方：小余積と幾何学的実現から小余極限を構成する一般 bar 図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {I : Type u} [Category.{u} I] (Y : I ⥤ Type u)

/-- 概要：同じ次数の離散ファイバーから持ち上げた元の左 Kan 添字への比較。
方針：通常の comma の nerve 比較と元の宇宙同型を合成する。
規約：元の指定次数を保持する。
使われ方：標的の小余積だけによる各局所余極限の存在。 -/
def elementsCoproductKanComparison (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete (Y.obj i))) ⟶
      leftKanShape ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y)))
        (ULift.up (nerveVertex i)) :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (elementsDegreeFiber Y i) ≫
      (F1B.nerveLeftKanShapeIso (Functor.Elements.π Y) i).hom) ≫
    (Idempotent.leftKanShapeUniverseIso (nerveMap (Functor.Elements.π Y)) (nerveVertex i)).hom

/-- 概要：同じ離散次数ファイバーによる元の局所添字の比較は right cofinal。
方針：明示的な comma の左随伴、nerve 同型、宇宙同型を合成する。
規約：小さい次数を別の同値類へ取り替えない。
使われ方：局所左 Kan 図式の余極限の存在を小余積から戻す。 -/
lemma elementsCoproductKanComparison_isRightCofinal (i : I) :
    IsRightCofinal (elementsCoproductKanComparison Y i) :=
  (Ind.isRightCofinal_ulift _ ((elementsDegreeFiber_nerve_isRightCofinal Y i).comp
    (isRightCofinal_of_isIso
      (F1B.nerveLeftKanShapeIso (Functor.Elements.π Y) i).hom))).comp
    (isRightCofinal_of_isIso
      (Idempotent.leftKanShapeUniverseIso (nerveMap (Functor.Elements.π Y))
        (nerveVertex i)).hom)

/-- 概要：小余積を持つ標的では、元の次数射影の全局所左 Kan 図式が余極限を持つ。
方針：離散ファイバーの小余積を構成し、同じ cofinal 比較で存在を戻す。
規約：元の図式は任意で、標的を前層圏に限定しない。
使われ方：次数ごとの小余積の coherent な全選択。 -/
lemma elementsCoproduct_leftKanDiagram_hasColimit
    {X : SSet.{u + 1}} [Quasicategory X] (hX : HasSmallCoproducts X)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Y.Elements) ⟶ X)
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌) :
    HasColimit (leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y))) F v) := by
  rcases v with ⟨v⟩
  obtain ⟨i, rfl⟩ := nerveEquiv.symm.surjective v
  apply hasColimit_of_rightCofinalRestriction (elementsCoproductKanComparison Y i)
    (elementsCoproductKanComparison_isRightCofinal Y i)
  exact hX (Y.obj i) _

/-- 概要：小余積だけから、要素圏の次数射影に沿う全左 Kan 延長が存在する。
方針：全局所余極限の存在を元の左 Kan 存在定理へ渡す。
規約：全ての次数の自然性を持つ単位を得る。
使われ方：小余積からの一般の単体的 bar 図式の構成。 -/
lemma elementsCoproduct_exists_leftKanExtension
    {X : SSet.{u + 1}} [Quasicategory X] (hX : HasSmallCoproducts X)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Y.Elements) ⟶ X) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ X)
      (β : SSet.Homotopy F
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y)) ≫ G)),
      IsLeftKanExtension
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y))) F G β :=
  F1B.exists_kanLeftExtension_of_local_colimits _ F
    (elementsCoproduct_leftKanDiagram_hasColimit Y hX F)

end SerrePositivity.InfinityCategories.F2.Presentable
