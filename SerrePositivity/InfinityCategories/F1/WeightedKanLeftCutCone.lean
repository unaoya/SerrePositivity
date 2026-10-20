module

public import SerrePositivity.InfinityCategories.F1.WeightedKanLeftCutTailMaps

/-!
概要：元の weighted 係数から、左区間の実際の対角単体を tail とする cone を構成する。
方針：head と tail を同じ対象表示へ正規化し、三つの時間分岐で既証明の合成則を使う。
規約：head の合成則は元の strict 変換から証明し、追加仮定として受け取らない。
使われ方：共通 weighted 始域の pointed prism を単体ごとに与える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
  SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

private lemma headComp_of_eq (x : KanObject.{u}) {X Y X' Y' : KanObject.{u}}
    (eX : X = X') (eY : Y = Y') {L M N : SSet.{u}} (m : L ⊗ M ⟶ N)
    (f : L ⟶ SimplicialCategory.sHom x X) (g : M ⟶ SimplicialCategory.sHom X Y)
    (h : N ⟶ SimplicialCategory.sHom x Y)
    (hn : m ≫ h ≫ eqToHom (congrArg (SimplicialCategory.sHom x) eY) =
      ((f ≫ eqToHom (congrArg (SimplicialCategory.sHom x) eX)) ⊗ₘ
        (g ≫ eqToHom (congrArg₂ SimplicialCategory.sHom eX eY))) ≫ eComp SSet x X' Y') :
    m ≫ h = (f ⊗ₘ g) ≫ eComp SSet x X Y := by
  subst X'
  subst Y'
  simpa only [eqToHom_refl, Category.comp_id] using hn

private lemma cutTime_one (w : Fin 2) (h : w ≠ 0) : w = 1 := by
  fin_cases w <;> simp_all

/-- 実際の weighted head は、元の左区間から構成した tail の全 Hom と合成を保つ。 -/
lemma weightedKanLeftCutHead_comp {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (i j : Fin (n + 1)) :
    eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ weightedKanLeftCutHead F G x σ τ s t j =
    (weightedKanLeftCutHead F G x σ τ s t i ⊗ₘ
      (coherentConeTailExtension (kanDiagramLeftHomCutSimplex F G σ s t)).map
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩) ≫
      eComp SSet x ((kanDiagramLeftHomCutSimplex F G σ s t).obj ⟨ULift.up i⟩)
        ((kanDiagramLeftHomCutSimplex F G σ s t).obj ⟨ULift.up j⟩) := by
  by_cases hij : i ≤ j
  · by_cases hi : (stdSimplex.objEquiv t).toOrderHom i = 0
    · by_cases hj : (stdSimplex.objEquiv t).toOrderHom j = 0
      · apply headComp_of_eq x
          (kanDiagramLeftHomCutSimplex_obj_zero F G σ s t i hi)
          (kanDiagramLeftHomCutSimplex_obj_zero F G σ s t j hj)
        rw [weightedKanLeftCutHead_zero F G x σ τ s t j hj,
          weightedKanLeftCutHead_zero F G x σ τ s t i hi,
          weightedKanLeftCutTail_zero F G σ s t i j hij hi hj]
        exact (weightedConeSimplex F.val x τ).map_comp
          (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
          ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩
      · have hj' := cutTime_one _ hj
        apply headComp_of_eq x
          (kanDiagramLeftHomCutSimplex_obj_zero F G σ s t i hi)
          (kanDiagramLeftHomCutSimplex_obj_one F G σ s t j hj')
        rw [weightedKanLeftCutHead_one F G x σ τ s t j hj',
          weightedKanLeftCutHead_zero F G x σ τ s t i hi,
          weightedKanLeftCutTail_mixed F G σ s t i j hij hi hj']
        exact weightedConeCutCoefficient_comp_zero F.val x τ
          (stdSimplex.objEquiv t).toOrderHom i j hi hj' (G.val.obj (σ.obj j))
          (SSet.yonedaEquiv.symm s ≫ SSet.opFunctor.map (strictDiagramMappingComponent
            (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) (σ.obj j)))
    · have hi' := cutTime_one _ hi
      have hjn : (stdSimplex.objEquiv t).toOrderHom j ≠ 0 := by
        intro hj
        have h := (stdSimplex.objEquiv t).toOrderHom.monotone hij
        rw [hi', hj] at h
        exact (by decide : ¬ (1 : Fin 2) ≤ 0) h
      have hj' := cutTime_one _ hjn
      apply headComp_of_eq x
        (kanDiagramLeftHomCutSimplex_obj_one F G σ s t i hi')
        (kanDiagramLeftHomCutSimplex_obj_one F G σ s t j hj')
      rw [weightedKanLeftCutHead_one F G x σ τ s t j hj',
        weightedKanLeftCutHead_one F G x σ τ s t i hi',
        weightedKanLeftCutTail_one F G σ s t i j hij hi' hj']
      exact weightedKanConeCutCoefficient_comp_one F.val G.val x τ s
        (stdSimplex.objEquiv t).toOrderHom i j hi' hj'
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact False.elim (hij (Fin.succ_le_succ_iff.mp
      (Path.le (J := ULift.{u} (Fin (n + 2))) (Q.obj 0))))

/-- 全ての head と実際の tail の合成則を、元の weighted データから証明付きで束ねる。 -/
def weightedKanLeftCutConeHead {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    CoherentConeHead x (coherentConeTailExtension (kanDiagramLeftHomCutSimplex F G σ s t)) where
  hom := weightedKanLeftCutHead F G x σ τ s t
  comp := weightedKanLeftCutHead_comp F G x σ τ s t

/-- 元の weighted 係数と元の strict 変換から、始点固定の実際の cone の全単体を作る。 -/
def weightedKanLeftCutConeSimplex {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) : SpaceInfinity.{u} _⦋n + 1⦌ :=
  coherentConeSimplexOfHead x _ (weightedKanLeftCutConeHead F G x σ τ s t)

/-- 構成した実際の cone の初点は、指定した同じ Kan 対象。 -/
lemma weightedKanLeftCutConeSimplex_apex {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (SimplicialNerve KanObject.{u}).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (weightedKanLeftCutConeSimplex F G x σ τ s t) = coherentNerveVertex x :=
  coherentConeSimplexOfHead_apex x _ (weightedKanLeftCutConeHead F G x σ τ s t)

/-- 構成した cone の tail は、同じ実際の左区間の対角評価を厳密に回収する。 -/
lemma weightedKanLeftCutConeSimplex_tail {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (SimplicialNerve KanObject.{u}).δ 0 (weightedKanLeftCutConeSimplex F G x σ τ s t) =
      kanDiagramLeftHomCutSimplex F G σ s t := by
  rw [weightedKanLeftCutConeSimplex, coherentConeSimplexOfHead_tail,
    coherentConeTailExtension_tail]

/-- 元の weighted 係数から、指定した始点の coslice の実際の全単体を作る。 -/
def weightedKanLeftCutCosliceSimplex {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x))) _⦋n⦌ := by
  refine ⟨(leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
    (weightedKanLeftCutConeSimplex F G x σ τ s t), ?_⟩
  rw [← Category.assoc, joinStdSimplexIso_leftPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left, weightedKanLeftCutConeSimplex_apex]

/-- coslice の同じ単体の射影は、元の左区間 prism の実際の対角評価。 -/
lemma weightedKanLeftCutCosliceSimplex_projection {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x))).app
      (Opposite.op ⦋n⦌) (weightedKanLeftCutCosliceSimplex F G x σ τ s t) =
      kanDiagramLeftHomCutSimplex F G σ s t := by
  change SSet.yonedaEquiv (joinInr Δ[0] Δ[n] ≫
    ((leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (weightedKanLeftCutConeSimplex F G x σ τ s t))) = _
  rw [← Category.assoc, joinStdSimplexIso_leftPoint_inr,
    stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]
  exact weightedKanLeftCutConeSimplex_tail F G x σ τ s t

end SerrePositivity.InfinityCategories
