module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeWeightedEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedRepresentableComparison

/-!
概要：反転した strict Hom 錐から coherent な錐への比較を全パラメータで評価する。
方針：切断・ULift・重み付き end の評価を順に戻し、実際の錐の脚の係数を得る。
規約：極限性や Kan 性なしで等式を示す。native な選択付き比較との一致は別工程。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB） の strict な錐の主比較の整合性。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：引き戻しの切断と相対関手の同型の順方向の評価は第一射影への後合成。
方針：同型の定義と相対 curry の評価を使う。
規約：全ての単体集合の射に適用し、充填性を要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の切断模型の標準比較の追跡。 -/
lemma pullbackSectionsRelativeIso_hom_uncurry {K E B : SSet.{u}}
    (p : E ⟶ B) (a : K ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.pullbackSectionsRelativeIso p a).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (pullback.snd p a) ≫ pullback.fst p a := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.pullbackSectionsRelativeIso]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry _ _

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：weighted nerve の切断比較を相対関手の族へ戻すと coslice 比較の後合成になる。
方針：切断の写像の評価と引き戻しの第一射影の式を使う。
規約：切断の全パラメータを扱い、点だけの同定に制限しない。
使われ方：HTT 4.2.4.1 の係数比較の実際の族の計算。 -/
lemma weightedCoherentConeSectionsComparison_uncurry (F : I ⥤ C) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentConeSectionsComparison F x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation ((SSet.uliftFunctor.{v, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F x := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentConeSectionsComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeSectionsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) := pullbackSectionsRelativeIso_hom_uncurry _ _
  rw [he, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_evaluation, Category.assoc]
  change _ ≫ (pullback.lift _ _ _ ≫ pullback.fst _ _) = _
  rw [pullback.lift_fst]

/-- 概要：反転 Hom の end の切断比較を評価すると weighted nerve の普遍評価になる。
方針：相対関手の評価、ULift 切断同型、end の切断同型の評価を順に使う。
規約：直積の ULift 同型を明示し、全パラメータの厳密な等式を示す。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の元の錐からの比較を計算する準備。 -/
lemma reflectedHomHolimConeComparison_uncurry (F : I ⥤ C) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F x) =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (nerve I)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor))).inv ≫
      (SSet.uliftFunctor.{v, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F x := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter,
    weightedCoherentConeSectionsComparison_uncurry]
  change (_ ◁ ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap _) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftSectionsComparison _)) ≫ (_ ≫ _) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftSectionsComparison_map_evaluation]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap_evaluation, Category.assoc]

/-- 概要：反転した strict Hom の比較の評価は実際の Hom 錐の脚から作る coslice の族。
方針：q′ の end での評価を、反転した錐の第二射影と脚の合成に戻す。
規約：全次数・全パラメータの等式。極限性や局所 Kan 性は不要。
使われ方：HTT 4.2.4.1 の strict な錐と coherent な錐の整合性の具体式。 -/
lemma reflectedStrictConeSectionsComparison_uncurry {F : I ⥤ C} (c : Cone F) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison c x) =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (nerve I) (SimplicialCategory.sHom x c.pt).op).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform
        (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) ((Functor.const I).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplicialHomCone c x).pt) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplicialHomCone c x).π)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F x := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter,
    reflectedHomHolimConeComparison_uncurry, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso_inv_whiskerLeft, Category.assoc]
  have he := congrArg (fun t : nerve I ⊗ (SimplicialCategory.sHom x c.pt).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) ↦
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (nerve I) (SimplicialCategory.sHom x c.pt).op).inv ≫
      (SSet.uliftFunctor.{v, u}).map t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_weightedNerveEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplicialHomCone c x))
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison, CategoryTheory.Functor.map_comp,
    Category.assoc] using he

/-- 概要：反転した strict Hom 錐の非定値係数は元の錐の脚の後合成である。
方針：初区間の係数の第二射影を計算し、反転の前合成・後合成の式を適用する。
規約：任意の Hom の高次単体 a と底の射列 σ を同時に扱う。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の錐の成分と高次の整合性を含む比較。 -/
lemma weightedCoherentCoefficient_strictCone {F : I ⥤ C} (c : Cone F) (x : C)
    {n : ℕ} (σ : ComposableArrows I n)
    (a : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom x c.pt).op)
    (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients
      (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) ((Functor.const I).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplicialHomCone c x).pt) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplicialHomCone c x).π) σ a) j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫
        SSet.opFunctor.map (SSet.stdSimplex.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap a ≫
        ((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map (c.π.app (σ.obj j)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveCoefficients_cone_app]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap
    (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n _) ≫ a ≫ SSet.opFunctor.map
      (((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map
        (c.π.app (σ.obj j)))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap_post]

/-- 概要：反転した strict Hom の切断比較は各対象で canonical な左 Hom 比較と整合する。
方針：底の頂点での weighted nerve の評価を錐の脚へ戻し、定値 fiber の比較を使う。
規約：全 Hom パラメータの射の等式。Kan 性・極限性・逆射の選択を要求しない。
使われ方：HTT 4.2.4.1 の strict な錐の成分と native な写像空間との接続。 -/
lemma reflectedStrictConeSectionsComparison_evaluate {F : I ⥤ C}
    (c : Cone F) (x : C) (i : I) :
    lift (SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)))
        (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison c x) =
    (SSet.uliftFunctor.{v, u}).map (SSet.opFunctor.map
        (((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map (c.π.app i))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison x (F.obj i) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj i)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.weightedConstantCosliceFiberMap_eq F x i]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.weightedConstantCosliceFiberMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.weightedConstantCosliceMap]
  rw [reflectedStrictConeSectionsComparison_uncurry, ← Category.assoc]
  have he : lift (SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)))
        (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (nerve I) (SimplicialCategory.sHom x c.pt).op).inv =
      (SSet.uliftFunctor.{v, u}).map
        (lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) (𝟙 (SimplicialCategory.sHom x c.pt).op)) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  rw [he]
  have hc := congrArg (fun t : (SimplicialCategory.sHom x c.pt).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) ↦
    (SSet.uliftFunctor.{v, u}).map t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromCone_constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplicialHomCone c x) i)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplicialHomCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone, Functor.mapCone,
    Cone.functoriality] at hc ⊢
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hc
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
