module

public import SerrePositivity.InfinityCategories.F1.KanDiagramLeftHomCutSimplex
public import SerrePositivity.InfinityCategories.F1.WeightedConeCutHomComposition
public import SerrePositivity.InfinityCategories.F1.StrictDiagramOppositeHom

/-!
概要：元の左区間の混合 Hom を、合成則を証明した weighted cone の tail Hom と同定する。
方針：strict 変換の全次数の自然性で前合成と後合成の二つの表示を照合する。
規約：実際の混合評価を使い、独立な写像空間比較に置き換えない。
使われ方：weighted prism の正頂点間の Hom を固定し、初点からの係数の合成則を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 切断後の tail Hom は、同じパラメーターの元の strict 混合評価に厳密に一致。 -/
lemma weightedConeCutTailHom_eq_strictMixed {I : Type u} [SmallCategory I]
    (F G : I ⥤ KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (strictDiagramMappingSpace (F ⋙ kanObjectForget) (G ⋙ kanObjectForget)).op _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (a b : Fin (n + 1)) (hab : a ≤ b) (hb : t b = 1) :
    weightedConeCutTailHom F σ t a b hb (G.obj (σ.obj b))
      (SSet.yonedaEquiv.symm s ≫ SSet.opFunctor.map
        (strictDiagramMappingComponent (F ⋙ kanObjectForget) (G ⋙ kanObjectForget) (σ.obj b))) =
    pathCutMinimumMap t hb ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm s) ≫
      strictDiagramMixedHom (σ.map (homOfLE hab)) (F ⋙ kanObjectForget) (G ⋙ kanObjectForget) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  let r := reflectedSimplexMap (SSet.yonedaEquiv.symm s)
  let θ := r.app (Opposite.op ⦋d⦌) ((pathCutMinimumMap t hb).app (Opposite.op ⦋d⦌) P)
  let f := σ.map (homOfLE hab)
  change (eComp SSet (F.obj (σ.obj a)) (F.obj (σ.obj b)) (G.obj (σ.obj b))).app
      (Opposite.op ⦋d⦌)
      (PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map f)) d, θ.val (σ.obj b)) =
    ((ihom (F.obj (σ.obj a)).obj).map (show (G.obj (σ.obj a)).obj ⟶
      (G.obj (σ.obj b)).obj from G.map f)).app (Opposite.op ⦋d⦌) (θ.val (σ.obj a))
  have hF : PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map f)) d =
      (eHomEquiv SSet (F.map f)).app (Opposite.op ⦋d⦌) PUnit.unit :=
    (unitHom_app_constant (eHomEquiv SSet (F.map f)) d).symm
  rw [hF]
  have hp : (eComp SSet (F.obj (σ.obj a)) (F.obj (σ.obj b)) (G.obj (σ.obj b))).app
      (Opposite.op ⦋d⦌)
      ((eHomEquiv SSet (F.map f)).app (Opposite.op ⦋d⦌) PUnit.unit, θ.val (σ.obj b)) =
    ((pre (show (F.obj (σ.obj a)).obj ⟶ (F.obj (σ.obj b)).obj from F.map f)).app
      (G.obj (σ.obj b)).obj).app (Opposite.op ⦋d⦌) (θ.val (σ.obj b)) := by
    exact congrArg (fun h => h.app (Opposite.op ⦋d⦌) (PUnit.unit, θ.val (σ.obj b)))
      (curry'_whiskerRight_comp (C := SSet.{u}) (Z := (G.obj (σ.obj b)).obj)
        (show (F.obj (σ.obj a)).obj ⟶ (F.obj (σ.obj b)).obj from F.map f))
  exact hp.trans (strictDiagramMappingSimplex_post_pre θ f).symm

/-- 元の共同評価の混合 Hom は、同じ正頂点への移送後の weighted tail Hom そのもの。 -/
lemma kanDiagramLeftHomCutSimplex_mixedHom_eq_tail {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (a b : Fin (n + 1)) (hab : a ≤ b)
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 0)
    (hb : (stdSimplex.objEquiv t).toOrderHom b = 1) :
    (kanDiagramLeftHomCutSimplex F G σ s t).map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (kanDiagramLeftHomCutSimplex_obj_zero F G σ s t a ha)
        (kanDiagramLeftHomCutSimplex_obj_one F G σ s t b hb)) =
    nerveMap (pathPositiveShiftFunctor a b) ≫
      weightedConeCutTailHom F.val σ (stdSimplex.objEquiv t).toOrderHom a b hb
        (G.val.obj (σ.obj b)) (SSet.yonedaEquiv.symm s ≫ SSet.opFunctor.map
          (strictDiagramMappingComponent (F.val ⋙ kanObjectForget)
            (G.val ⋙ kanObjectForget) (σ.obj b))) := by
  have h := kanDiagramLeftHomCutSimplex_mixedHom F G σ s t a b hab ha hb
  have e := congrArg (fun f => nerveMap (pathPositiveShiftFunctor a b) ≫ f)
    (weightedConeCutTailHom_eq_strictMixed F.val G.val σ s (stdSimplex.objEquiv t).toOrderHom
      a b hab hb)
  exact h.trans e.symm

end SerrePositivity.InfinityCategories
