module

public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeWeightedEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedRepresentableComparison

/-!
概要：反転した strict Hom 錐から coherent な錐への比較を全パラメータで評価する。
方針：切断・ULift・重み付き end の評価を順に戻し、実際の錐の脚の係数を得る。
規約：極限性や Kan 性なしで等式を示す。native な選択付き比較との一致は別工程。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6 の strict な錐の主比較の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：引き戻しの切断と相対関手の同型の順方向の評価は第一射影への後合成。
方針：同型の定義と相対 curry の評価を使う。
規約：全ての単体集合の射に適用し、充填性を要求しない。
使われ方：Kerodon 7.4.1.6 の切断模型の標準比較の追跡。 -/
lemma pullbackSectionsRelativeIso_hom_uncurry {K E B : SSet.{u}}
    (p : E ⟶ B) (a : K ⟶ B) :
    relativeFunctorUncurry (pullbackSectionsRelativeIso p a).hom =
      simplicialSectionsEvaluation (pullback.snd p a) ≫ pullback.fst p a := by
  dsimp only [pullbackSectionsRelativeIso]
  exact relativeFunctorUncurry_curry _ _

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：weighted nerve の切断比較を相対関手の族へ戻すと coslice 比較の後合成になる。
方針：切断の写像の評価と引き戻しの第一射影の式を使う。
規約：切断の全パラメータを扱い、点だけの同定に制限しない。
使われ方：HTT 4.2.4.1 の係数比較の実際の族の計算。 -/
lemma weightedCoherentConeSectionsComparison_uncurry (F : I ⥤ C) (x : C) :
    relativeFunctorUncurry (weightedCoherentConeSectionsComparison F x) =
      simplicialSectionsEvaluation ((SSet.uliftFunctor.{v, u}).map
        (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor))) ≫
      weightedCosliceComparison F x := by
  rw [weightedCoherentConeSectionsComparison, relativeFunctorUncurry_parameter]
  have he : relativeFunctorUncurry
      (coherentConeSectionsIso (strictCoherentDiagram F) (coherentNerveVertex x)).hom =
      simplicialSectionsEvaluation
        (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x)) ≫
      pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (strictCoherentDiagram F) := pullbackSectionsRelativeIso_hom_uncurry _ _
  rw [he, ← Category.assoc,
    simplicialSectionsMap_evaluation, Category.assoc]
  change _ ≫ (pullback.lift _ _ _ ≫ pullback.fst _ _) = _
  rw [pullback.lift_fst]

/-- 概要：反転 Hom の end の切断比較を評価すると weighted nerve の普遍評価になる。
方針：相対関手の評価、ULift 切断同型、end の切断同型の評価を順に使う。
規約：直積の ULift 同型を明示し、全パラメータの厳密な等式を示す。
使われ方：Kerodon 7.5.4.6 の元の錐からの比較を計算する準備。 -/
lemma reflectedHomHolimConeComparison_uncurry (F : I ⥤ C) (x : C) :
    relativeFunctorUncurry (reflectedHomHolimConeComparison F x) =
      (uliftTensorIso (nerve I)
        (bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor))).inv ≫
      (SSet.uliftFunctor.{v, u}).map
        (bousfieldKanWeightedNerveEvaluation (simplicialHomDiagram F x ⋙ SSet.opFunctor)) ≫
      weightedCosliceComparison F x := by
  rw [reflectedHomHolimConeComparison, relativeFunctorUncurry_parameter,
    weightedCoherentConeSectionsComparison_uncurry]
  change (_ ◁ ((SSet.uliftFunctor.{v, u}).map (bousfieldKanSectionsMap _) ≫
      uliftSectionsComparison _)) ≫ (_ ≫ _) = _
  rw [← Category.assoc, uliftSectionsComparison_map_evaluation]
  rw [bousfieldKanSectionsMap_evaluation, Category.assoc]

/-- 概要：反転した strict Hom の比較の評価は実際の Hom 錐の脚から作る coslice の族。
方針：q′ の end での評価を、反転した錐の第二射影と脚の合成に戻す。
規約：全次数・全パラメータの等式。極限性や局所 Kan 性は不要。
使われ方：HTT 4.2.4.1 の strict な錐と coherent な錐の整合性の具体式。 -/
lemma reflectedStrictConeSectionsComparison_uncurry {F : I ⥤ C} (c : Cone F) (x : C) :
    relativeFunctorUncurry (reflectedStrictConeSectionsComparison c x) =
      (uliftTensorIso (nerve I) (SimplicialCategory.sHom x c.pt).op).inv ≫
      (SSet.uliftFunctor.{v, u}).map (weightedNerveSectionFromTransform
        (snd (bousfieldKanWeight I) ((Functor.const I).obj
          (reflectedSimplicialHomCone c x).pt) ≫ (reflectedSimplicialHomCone c x).π)) ≫
      weightedCosliceComparison F x := by
  rw [reflectedStrictConeSectionsComparison, relativeFunctorUncurry_parameter,
    reflectedHomHolimConeComparison_uncurry, ← Category.assoc,
    uliftTensorIso_inv_whiskerLeft, Category.assoc]
  have he := congrArg (fun t : nerve I ⊗ (SimplicialCategory.sHom x c.pt).op ⟶
      weightedNerve (simplicialHomDiagram F x ⋙ SSet.opFunctor) ↦
    (uliftTensorIso (nerve I) (SimplicialCategory.sHom x c.pt).op).inv ≫
      (SSet.uliftFunctor.{v, u}).map t ≫ weightedCosliceComparison F x)
    (bousfieldKanConeComparison_weightedNerveEvaluation (reflectedSimplicialHomCone c x))
  simpa only [reflectedRepresentableComparison, CategoryTheory.Functor.map_comp,
    Category.assoc] using he

/-- 概要：反転した strict Hom 錐の非定値係数は元の錐の脚の後合成である。
方針：初区間の係数の第二射影を計算し、反転の前合成・後合成の式を適用する。
規約：任意の Hom の高次単体 a と底の射列 σ を同時に扱う。
使われ方：Kerodon 7.5.4.6 の錐の成分と高次の整合性を含む比較。 -/
lemma weightedCoherentCoefficient_strictCone {F : I ⥤ C} (c : Cone F) (x : C)
    {n : ℕ} (σ : ComposableArrows I n)
    (a : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom x c.pt).op)
    (j : Fin (n + 1)) :
    weightedCoherentCoefficient (weightedNerveCoefficients
      (snd (bousfieldKanWeight I) ((Functor.const I).obj
        (reflectedSimplicialHomCone c x).pt) ≫ (reflectedSimplicialHomCone c x).π) σ a) j =
      pathFirstMinimumMap j ≫
        SSet.opFunctor.map (SSet.stdSimplex.map
          (simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt))) ≫
        reflectedSimplexMap a ≫
        ((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map (c.π.app (σ.obj j)) := by
  unfold weightedCoherentCoefficient
  rw [weightedNerveCoefficients_cone_app]
  change pathFirstMinimumMap j ≫ reflectedSimplexMap
    (SSet.stdSimplex.map (simplexPrefixInclusion j.val n _) ≫ a ≫ SSet.opFunctor.map
      (((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map
        (c.π.app (σ.obj j)))) = _
  rw [reflectedSimplexMap_pre, reflectedSimplexMap_post]

/-- 概要：反転した strict Hom の切断比較は各対象で canonical な左 Hom 比較と整合する。
方針：底の頂点での weighted nerve の評価を錐の脚へ戻し、定値 fiber の比較を使う。
規約：全 Hom パラメータの射の等式。Kan 性・極限性・逆射の選択を要求しない。
使われ方：HTT 4.2.4.1 の strict な錐の成分と native な写像空間との接続。 -/
lemma reflectedStrictConeSectionsComparison_evaluate {F : I ⥤ C}
    (c : Cone F) (x : C) (i : I) :
    lift (SSet.const (ULift.up (nerveVertex i)))
        (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op)) ≫
      relativeFunctorUncurry (reflectedStrictConeSectionsComparison c x) =
    (SSet.uliftFunctor.{v, u}).map (SSet.opFunctor.map
        (((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map (c.π.app i))) ≫
      coherentCosliceFiberComparison x (F.obj i) ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex (F.obj i)) := by
  rw [← weightedConstantCosliceFiberMap_eq F x i]
  rw [weightedConstantCosliceFiberMap, vertexFiberLift_ι, weightedConstantCosliceMap]
  rw [reflectedStrictConeSectionsComparison_uncurry, ← Category.assoc]
  have he : lift (SSet.const (ULift.up (nerveVertex i)))
        (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op)) ≫
      (uliftTensorIso (nerve I) (SimplicialCategory.sHom x c.pt).op).inv =
      (SSet.uliftFunctor.{v, u}).map
        (lift (SSet.const (nerveVertex i)) (𝟙 (SimplicialCategory.sHom x c.pt).op)) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  rw [he]
  have hc := congrArg (fun t : (SimplicialCategory.sHom x c.pt).op ⟶
      weightedNerve (simplicialHomDiagram F x ⋙ SSet.opFunctor) ↦
    (SSet.uliftFunctor.{v, u}).map t ≫ weightedCosliceComparison F x)
    (weightedNerveSectionFromCone_constant (reflectedSimplicialHomCone c x) i)
  dsimp only [reflectedSimplicialHomCone, simplicialHomCone, Functor.mapCone,
    Cone.functoriality] at hc ⊢
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hc
  exact hc

end SerrePositivity.InfinityCategories.HomotopyLimits
