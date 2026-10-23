module

public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointHomEnriched
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedSpaceLeftResolutionCompatibility
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOppositeKanEnriched

/-!
概要：左 fiber の反転した一点 Hom 係数のパラメーター付き作用。
方針：元の写像を反転し、一点 Hom に作用させてから再び反転する。
規約：対象の二つの反転に合わせてパラメーターも二度反転し、元のパラメーターを保つ。
使われ方：Kerodon §4.6.7、Corollary 5.6.0.6、具体的な左 fiber 比較の高次の係数の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：一点 Hom の標準同型は任意のパラメーター付き写像の後合成と可換。
方針：豊穣な比較の可換式をパラメーターの curry で引き戻し、評価の往復を消す。
規約：パラメーター T 自身の Kan 性は不要。
使われ方：Kerodon Corollary 5.6.0.6、反転する前の一点 Hom の係数の自然性。 -/
lemma kanPointHomParameterizedMap_comparison {X Y : KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    ((ihom pointKanObject.obj).obj X.obj ◁ curry f) ≫
        MonoidalClosed.comp pointKanObject.obj X.obj Y.obj ≫ (pointKanObjectHomIso Y).hom =
      ((pointKanObjectHomIso X).hom ▷ T) ≫ f := by
  have h := kanPointHomEnrichedComparison.property X Y
  change ((pointKanObjectHomIso X).hom ▷ (ihom X.obj).obj Y.obj) ≫
      uncurry (𝟙 ((ihom X.obj).obj Y.obj)) =
    uncurry (curry (MonoidalClosed.comp pointKanObject.obj X.obj Y.obj)) ≫
      (pointKanObjectHomIso Y).hom at h
  rw [uncurry_curry] at h
  rw [← h, whisker_exchange_assoc]
  congr 1
  change uncurry (curry f ≫ 𝟙 ((ihom X.obj).obj Y.obj)) = f
  rw [Category.comp_id, uncurry_curry]

/-- 概要：反転した一点 Hom 係数に任意のパラメーター付き写像を作用させる。
方針：写像とパラメーターを反転し、内部 Hom の合成の後で再び反転する。
規約：X・Y・T の Kan 性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6、左 Hom の実際の係数の豊穣作用。 -/
noncomputable def leftPointHomParameterizedMap {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    ((ihom pointKanObject.obj).obj X.op).op ⊗ T ⟶
      ((ihom pointKanObject.obj).obj Y.op).op :=
  (((ihom pointKanObject.obj).obj X.op).op ◁
      (SSet.opFunctorCompOpFunctorIso.app T).inv) ≫
    (HomotopyLimits.oppositeTensorIso ((ihom pointKanObject.obj).obj X.op) T.op).inv ≫
    SSet.opFunctor.map
      (((ihom pointKanObject.obj).obj X.op ◁
        curry ((HomotopyLimits.oppositeTensorIso X T).inv ≫ SSet.opFunctor.map f)) ≫
        MonoidalClosed.comp pointKanObject.obj X.op Y.op)

/-- 概要：反転した一点 Hom 係数から元の空間への標準同型はパラメーター付き作用と可換。
方針：一点空間からの Hom の標準同型を内部 Hom の合成で評価し、二重反転を消す。
規約：同型は既存の pointedSpaceLeftCoefficientIso の逆方向。
使われ方：Kerodon Corollary 5.6.0.6、左 fiber の係数の全パラメーターに関する自然性。 -/
lemma leftPointHomParameterizedMap_comparison {X Y : KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    leftPointHomParameterizedMap f ≫ (pointedSpaceLeftCoefficientIso Y).inv =
      ((pointedSpaceLeftCoefficientIso X).inv ▷ T) ≫ f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  have h := kanPointHomParameterizedMap_comparison
    (X := kanObjectOpFunctor.obj X) (Y := kanObjectOpFunctor.obj Y)
    ((HomotopyLimits.oppositeTensorIso X.obj T).inv ≫ SSet.opFunctor.map f)
  have hv := congrArg (fun g : (ihom pointKanObject.obj).obj X.obj.op ⊗ T.op ⟶ Y.obj.op ↦
    g.app (SimplexCategory.rev.op.obj n) (SSet.opObjEquiv x, SSet.opObjEquiv.symm t)) h
  exact congrArg SSet.opObjEquiv hv

/-- 概要：反転した一点 Hom 係数を取る作用は Kan 複体の豊穣自己関手。
方針：二重反転したパラメーター付き評価を curry し、各 Hom の単位・合成を計算する。
規約：対象は既存の左 fiber 比較の始域の係数そのもの。
使われ方：Kerodon Corollary 5.6.0.6、左 fiber の係数を任意の coherent な図式に適用する。 -/
noncomputable def leftPointHomKanEnriched :
    EnrichedFunctor SSet.{u} KanObject.{u} KanObject.{u} where
  obj X := ⟨((ihom pointKanObject.obj).obj X.obj.op).op, inferInstance⟩
  map X Y := curry (leftPointHomParameterizedMap (uncurry (𝟙 ((ihom X.obj).obj Y.obj))))
  map_id X := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    apply SSet.opObjEquiv.injective
    apply Functor.HomObj.ext
    funext m α
    apply ConcreteCategory.hom_ext
    intro z
    change (SSet.opObjEquiv x).app m (α ≫ 𝟙 m) z = (SSet.opObjEquiv x).app m α z
    rw [Category.comp_id]
  map_comp X Y Z := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, f, g⟩
    apply SSet.opObjEquiv.injective
    apply Functor.HomObj.ext
    funext m α
    apply ConcreteCategory.hom_ext
    intro z
    rfl

/-- 概要：反転した一点 Hom 係数から元の空間への標準同型は豊穣な比較。
方針：パラメーター付きの可換式を内部 Hom の評価に適用する。
規約：各成分は pointedSpaceLeftCoefficientIso の逆方向そのもの。
使われ方：Kerodon Corollary 5.6.0.6、左 fiber の係数の coherent な正規化。 -/
noncomputable def leftPointHomKanComparison :
    KanEnrichedComparison leftPointHomKanEnriched
      (EnrichedFunctor.id SSet.{u} KanObject.{u}) := by
  refine ⟨(fun X ↦ show leftPointHomKanEnriched.obj X ⟶ X from
    (pointedSpaceLeftCoefficientIso X).inv), ?_⟩
  intro X Y
  change ((pointedSpaceLeftCoefficientIso X).inv ▷ (ihom X.obj).obj Y.obj) ≫
      uncurry (𝟙 ((ihom X.obj).obj Y.obj)) =
    uncurry (curry (leftPointHomParameterizedMap
      (uncurry (𝟙 ((ihom X.obj).obj Y.obj))))) ≫ (pointedSpaceLeftCoefficientIso Y).inv
  rw [uncurry_curry]
  exact (leftPointHomParameterizedMap_comparison _).symm

/-- 概要：左 fiber の反転した一点 Hom 係数の作用を空間の coherent nerve へ移す。
方針：パラメーターを二重反転して構成した豊穣自己関手に coherent nerve を適用する。
規約：単独の反転を元の内部 Hom からの豊穣関手とは見なさない。
使われ方：Kerodon Corollary 5.6.0.6、任意の coherent な図式での左 fiber 係数。 -/
noncomputable def leftPointHomInfinityMap : SpaceInfinity.{u} ⟶ SpaceInfinity.{u} :=
  coherentNerveMap leftPointHomKanEnriched

/-- 概要：反転した一点 Hom 係数の自己写像は空間の恒等写像と関手同型。
方針：標準の係数の同型の豊穣な比較を coherent な関手同型にする。
規約：対象ごとの比較の族ではなく関手空間内で比較する。
使われ方：Kerodon Corollary 5.6.0.6、左 fiber の係数の全ての高次の自然性。 -/
noncomputable def leftPointHomInfinityComparisonIso :
    FunctorIso leftPointHomInfinityMap.{u} (𝟙 SpaceInfinity.{u}) := by
  have h := kanEnrichedComparisonIso leftPointHomKanComparison
    (fun X ↦ (qCatEquivalenceOfIso (pointedSpaceLeftCoefficientIso X).symm).isQCatEquivalence)
  rw [coherentNerveMap_id] at h
  exact h

/-- 概要：任意の coherent な空間値図式の左 fiber 係数は元の図式と関手同型。
方針：空間全体の豊穣な係数の比較を元の図式に沿って引き戻す。
規約：底の quasicategory 性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6、復元比較の係数の高次の整合性。 -/
noncomputable def leftPointHomDiagramComparisonIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) : FunctorIso (F ≫ leftPointHomInfinityMap) F := by
  have h := leftPointHomInfinityComparisonIso.precomp F
  rw [Category.comp_id] at h
  exact h

end SerrePositivity.InfinityCategories
