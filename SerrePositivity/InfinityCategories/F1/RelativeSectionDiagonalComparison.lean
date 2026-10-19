module

public import SerrePositivity.InfinityCategories.F1.RelativeSectionDiagramComparison

/-!
概要：定義域図式の比較を、添字と全 left fibrations の同時対角評価で保つ。
方針：豊穣自然性と添字の自然性を合成して Kan 値豊穣比較を作る。
規約：高次の Hom と単体の添字を同時に動かす。
使われ方：切断図式全体の比較を coherent な一つの族へ実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：切断の比較は添字の射と高次の相対射を同時に評価しても自然。
方針：豊穣自然性に続けて終域の比較の添字自然性を使う。
規約：パラメーターの次数と評価の次数は独立。
使われ方：同時対角評価での比較の豊穣自然性。 -/
lemma relativeSectionDiagramComparison_mixedNaturality
    {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) (p q : LeftFibrationObject B)
    {i j : J} (f : i ⟶ j) {n k : SimplexCategoryᵒᵖ}
    (θ : (SimplicialCategory.sHom p q).obj n) (α : n ⟶ k)
    (x : (relativeFunctorSpace p.val.hom (D.obj (Opposite.op i)).hom).obj k) :
    (((relativeSectionEnrichedDiagram A).evaluate q ⋙ kanObjectForget).map f).app k
      (((((relativeSectionEnrichedDiagram A).mappingSpaceMap p q).app n θ).val i).app k α
        (((relativeSectionDiagramComparison η p).app i).app k x)) =
    ((relativeSectionDiagramComparison η q).app j).app k
      ((((relativeSectionEnrichedDiagram D).evaluate q ⋙ kanObjectForget).map f).app k
        (((((relativeSectionEnrichedDiagram D).mappingSpaceMap p q).app n θ).val i).app k
          α x)) := by
  have h := congrArg (fun m ↦ (((m.app n θ).val i).app k α x))
    (relativeSectionDiagramComparison_enrichedNaturality η p q)
  change ((relativeSectionDiagramComparison η q).app i).app k
      (((((relativeSectionEnrichedDiagram D).mappingSpaceMap p q).app n θ).val i).app k α x) =
    (((((relativeSectionEnrichedDiagram A).mappingSpaceMap p q).app n θ).val i).app k
      (α ≫ 𝟙 k)) (((relativeSectionDiagramComparison η p).app i).app k x) at h
  simp only [Category.comp_id] at h
  rw [← h]
  exact (congrArg (fun t ↦ t.app k
    (((((relativeSectionEnrichedDiagram D).mappingSpaceMap p q).app n θ).val i).app k α x))
    ((relativeSectionDiagramComparison η q).naturality f)).symm

/-- 概要：共同対角評価の間の切断制限は Kan 値豊穣比較。
方針：各対角の頂点で定義域の比較を取り、混合自然性を高次の Hom に適用する。
規約：coherent な対象図式も線形添字の底図式も任意。
使われ方：比較の二点図式を全次数で実現する入力。 -/
def relativeSectionDiagonalKanComparison
    {B : SSet.{u}} {J I : Type u} [Category.{u} J] [LinearOrder I]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) (σ : I ⥤ J)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) (LeftFibrationObject B)) :
    KanEnrichedComparison
      (diagonalKanDiagramEvaluation σ
        (T.comp SSet (relativeSectionEnrichedDiagram D).toEnrichedFunctor))
      (diagonalKanDiagramEvaluation σ
        (T.comp SSet (relativeSectionEnrichedDiagram A).toEnrichedFunctor)) := by
  refine ⟨(fun i ↦ (relativeSectionDiagramComparison η (T.obj i)).app (σ.obj i.as)), ?_⟩
  intro i j
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, P⟩
  have hij := SimplicialThickening.Path.le (P.obj 0)
  change ((diagonalKanDiagramHom σ
      (T.comp SSet (relativeSectionEnrichedDiagram A).toEnrichedFunctor) i j).app n P).app n
        (𝟙 n) (((relativeSectionDiagramComparison η (T.obj i)).app (σ.obj i.as)).app n x) =
    ((relativeSectionDiagramComparison η (T.obj j)).app (σ.obj j.as)).app n
      (((diagonalKanDiagramHom σ
        (T.comp SSet (relativeSectionEnrichedDiagram D).toEnrichedFunctor) i j).app n P).app n
          (𝟙 n) x)
  rw [diagonalKanDiagramHom_of_le _ _ i j hij, diagonalKanDiagramHom_of_le _ _ i j hij]
  exact relativeSectionDiagramComparison_mixedNaturality η (T.obj i) (T.obj j)
    (σ.map (homOfLE hij)) ((T.map i j).app n P) (𝟙 n) x

/-- 概要：共同対角評価の比較を二点の Kan 図式に束ねる。
方針：定義域図式の豊穣自然な比較から既存の二点図式を作る。
規約：同じ比較の成分をそのまま使う。
使われ方：全パラメーターの比較の共同実現。 -/
def relativeSectionDiagonalArrow
    {B : SSet.{u}} {J I : Type u} [Category.{u} J] [LinearOrder I]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) (σ : I ⥤ J)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) (LeftFibrationObject B)) :
    EnrichedFunctor SSet.{u} (SimplicialThickening I)
      (KanDiagramObject (ULift.{u} (Fin 2))) :=
  kanEnrichedComparisonArrowEnriched (relativeSectionDiagonalKanComparison η σ T)

/-- 概要：比較の二点図式は添字の同時制限と厳密に可換。
方針：二つの成分で対角 Hom の添字変換則を計算する。
規約：全ての単調写像、面、退化を含む。
使われ方：共同実現の単体的自然性。 -/
lemma relativeSectionDiagonalArrow_reindex
    {B : SSet.{u}} {J I K : Type u} [Category.{u} J] [LinearOrder I] [LinearOrder K]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) (α : I →o K) (σ : K ⥤ J)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening K) (LeftFibrationObject B)) :
    (SimplicialThickening.functor α).comp SSet (relativeSectionDiagonalArrow η σ T) =
      relativeSectionDiagonalArrow η (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet T) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  apply Subtype.ext
  funext t
  rcases t with ⟨t⟩
  fin_cases t
  · let F := T.comp SSet (relativeSectionEnrichedDiagram D).toEnrichedFunctor
    have hij := SimplicialThickening.Path.le (P.obj 0)
    change (((SimplicialThickening.functor α).map i j ≫
      diagonalKanDiagramHom σ F ((SimplicialThickening.functor α).obj i)
        ((SimplicialThickening.functor α).obj j)).app n) P =
      (diagonalKanDiagramHom (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet F) i j).app n P
    erw [diagonalKanDiagramHom_of_le σ F _ _ (α.monotone hij),
      diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl
  · let F := T.comp SSet (relativeSectionEnrichedDiagram A).toEnrichedFunctor
    have hij := SimplicialThickening.Path.le (P.obj 0)
    change (((SimplicialThickening.functor α).map i j ≫
      diagonalKanDiagramHom σ F ((SimplicialThickening.functor α).obj i)
        ((SimplicialThickening.functor α).obj j)).app n) P =
      (diagonalKanDiagramHom (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet F) i j).app n P
    erw [diagonalKanDiagramHom_of_le σ F _ _ (α.monotone hij),
      diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl

/-- 概要：底を固定した共同対角比較は既存の一対象の比較へ戻る。
方針：底の恒等射で混合 Hom を成分評価へ簡約する。
規約：比較の二点図式そのものの厳密な等式。
使われ方：全パラメーターの比較の点ごとの可逆性を検証する。 -/
lemma relativeSectionDiagonalArrow_constant
    {B : SSet.{u}} {J I : Type u} [Category.{u} J] [LinearOrder I]
    {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D) (j : J)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) (LeftFibrationObject B)) :
    relativeSectionDiagonalArrow η ((Functor.const I).obj j) T =
      T.comp SSet (kanEnrichedComparisonArrowEnriched
        (relativeFunctorOverPreComparison (η.app (Opposite.op j)))) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i k
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  apply Subtype.ext
  funext t
  rcases t with ⟨t⟩
  fin_cases t
  · let F := T.comp SSet (relativeSectionEnrichedDiagram D).toEnrichedFunctor
    change (diagonalKanDiagramHom ((Functor.const I).obj j) F i k).app n P = _
    rw [diagonalKanDiagramHom_of_le _ F i k
      (SimplicialThickening.Path.le (P.obj 0))]
    change ((F.map i k ≫ strictDiagramMixedHom (𝟙 j)
      ((F.obj i).val ⋙ kanObjectForget) ((F.obj k).val ⋙ kanObjectForget)).app n) P = _
    rw [kanDiagramMixedHom_base_id]
    rfl
  · let F := T.comp SSet (relativeSectionEnrichedDiagram A).toEnrichedFunctor
    change (diagonalKanDiagramHom ((Functor.const I).obj j) F i k).app n P = _
    rw [diagonalKanDiagramHom_of_le _ F i k
      (SimplicialThickening.Path.le (P.obj 0))]
    change ((F.map i k ≫ strictDiagramMixedHom (𝟙 j)
      ((F.obj i).val ⋙ kanObjectForget) ((F.obj k).val ⋙ kanObjectForget)).app n) P = _
    rw [kanDiagramMixedHom_base_id]
    rfl

end SerrePositivity.InfinityCategories
