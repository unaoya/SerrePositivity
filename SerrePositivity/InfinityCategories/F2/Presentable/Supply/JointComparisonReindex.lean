module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.JointRealizationPrecomposition

/-!
概要：共同図式比較の添字制限を、元の共同族の第一変数の制限へ同定する。
方針：全共同単体の同時対角評価を比較し、元の比較辺の像を回収する。
規約：元の比較と元の添字関手を保持する。
使われ方：P-12 の単体添字の制限と指定 straightening 底変換の合成との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の共同比較を任意の添字関手で制限する。
方針：添字の対象と射を元の比較へ送る。
規約：全高次 Hom の自然性を保持する。使われ方：単体添字の制限の共同実現。 -/
def jointComparisonReindex
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J K : Type u} [Category.{u} J] [Category.{u} K]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) (k : K ⥤ J) :
    KanEnrichedDiagramComparison (D.reindex k) (E.reindex k) where
  component j := η.component (k.obj j)
  naturality f X := η.naturality (k.map f) X

/-- 概要：添字制限した共同評価は元の共同評価の第一変数制限。
方針：元の対角評価の再添字付けの公式を使う。
規約：全共同単体の等式。使われ方：制限後の指定比較の両端の同定。 -/
lemma jointEvaluation_reindex
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J K : Type u} [Category.{u} J] [Category.{u} K]
    (D : KanEnrichedDiagram C J) (k : K ⥤ J) :
    (D.reindex k).jointEvaluation =
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ⊗ₘ 𝟙 (SimplicialNerve C)) ≫
        D.jointEvaluation := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  exact D.reindex_diagonal k (kanDiagramSimplexBase σ.down) T

/-- 概要：共同比較の二点対角図式は元の添字制限と厳密に両立する。
方針：二つの成分の全高次 Hom を元の混合対角評価へ戻す。
規約：任意の線形添字と対象図式を許す。使われ方：比較族の添字制限の同定。 -/
lemma jointComparisonDiagonalArrow_reindex
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J K I : Type u} [Category.{u} J] [Category.{u} K] [LinearOrder I]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E)
    (k : K ⥤ J) (σ : I ⥤ K)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    (jointComparisonReindex η k).diagonalArrow σ T = η.diagonalArrow (σ ⋙ k) T := by
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
  all_goals have hij := SimplicialThickening.Path.le (P.obj 0)
  · change (diagonalKanDiagramHom σ
      (T.comp SSet (D.reindex k).toEnrichedFunctor) i j).app n P =
      (diagonalKanDiagramHom (σ ⋙ k) (T.comp SSet D.toEnrichedFunctor) i j).app n P
    rw [diagonalKanDiagramHom_of_le _ _ i j hij, diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl
  · change (diagonalKanDiagramHom σ
      (T.comp SSet (E.reindex k).toEnrichedFunctor) i j).app n P =
      (diagonalKanDiagramHom (σ ⋙ k) (T.comp SSet E.toEnrichedFunctor) i j).app n P
    rw [diagonalKanDiagramHom_of_le _ _ i j hij, diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl

/-- 概要：制限した共同比較族は元の族の第一変数の制限。
方針：元の二点対角図式の等式を全単体で使う。
規約：元の比較族を保持する。使われ方：指定比較辺の添字制限。 -/
lemma jointComparisonFamily_reindex
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J K : Type u} [Category.{u} J] [Category.{u} K]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) (k : K ⥤ J) :
    (jointComparisonReindex η k).jointComparisonFamily =
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ⊗ₘ 𝟙 (SimplicialNerve C)) ≫
        η.jointComparisonFamily := by
  unfold KanEnrichedDiagramComparison.jointComparisonFamily
  rw [← Category.assoc]
  apply congrArg (fun f ↦ f ≫ kanDiagramRealization (ULift.{u} (Fin 2)))
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  exact jointComparisonDiagonalArrow_reindex η k (kanDiagramSimplexBase σ.down) T

/-- 概要：制限した共同比較辺は元の比較辺の内部前合成による像。
方針：共同族の添字制限の式を転置し同じ添字辺を写す。
規約：一単体そのものの等式。使われ方：指定比較 Hom の添字制限の正規化。 -/
lemma jointComparisonEdge_reindex_edge
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J K : Type u} [Category.{u} J] [Category.{u} K]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) (k : K ⥤ J) :
    (jointComparisonReindex η k).jointComparisonEdge.edge =
      (η.jointComparisonEdge.map ((pre
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ⊗ₘ 𝟙 (SimplicialNerve C))).app
          SpaceInfinity.{u})).edge := by
  change (transposeFunctorFamily (jointComparisonReindex η k).jointComparisonFamily).app
      (Opposite.op ⦋1⦌) coherentResolutionComparisonIndexEdge.edge =
    (((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ⊗ₘ
      𝟙 (SimplicialNerve C))).app SpaceInfinity.{u}).app (Opposite.op ⦋1⦌))
        ((transposeFunctorFamily η.jointComparisonFamily).app
          (Opposite.op ⦋1⦌) coherentResolutionComparisonIndexEdge.edge)
  rw [jointComparisonFamily_reindex, transposeFunctorFamily_comp]
  rfl

/-- 概要：制限した共同比較の Hom は元の比較 Hom の同じ内部前合成。
方針：元の辺の像を同じ端点へ移送して Hom 類に送る。
規約：全図式の Hom の等式。使われ方：指定比較同型の添字制限の正規化。 -/
lemma jointComparisonHom_reindex
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J K : Type u} [Category.{u} J] [Category.{u} K]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) (k : K ⥤ J) :
    F1B.kanFunctorHomCongr (jointEvaluation_reindex D k).symm
      (jointEvaluation_reindex E k).symm
      (precomposeFunctorHom
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ⊗ₘ 𝟙 (SimplicialNerve C))
        (Truncated.HomotopyCategory.homMk η.jointComparisonEdge.toTruncated)) =
      Truncated.HomotopyCategory.homMk
        (jointComparisonReindex η k).jointComparisonEdge.toTruncated := by
  rw [kanFunctorHomCongr_precompose_normalized, normalizedVertexHomMap_homMk]
  apply congrArg Truncated.HomotopyCategory.homMk
  apply Truncated.Edge.ext
  exact (jointComparisonEdge_reindex_edge η k).symm

/-- 概要：添字制限は元の共同比較の成分の同値性を保つ。
方針：元の比較を添字関手の対象で評価する。
規約：元の成分を保持する。使われ方：制限した指定比較同型の可逆性入力。 -/
lemma jointComparisonReindex_isQCatEquivalence
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J K : Type u} [Category.{u} J] [Category.{u} K]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) (k : K ⥤ J)
    (hη : ∀ j (p : C), IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p))
    (j : K) (p : C) :
    IsQCatEquivalence (X := (((D.reindex k).obj j).obj p).obj)
      (Y := (((E.reindex k).obj j).obj p).obj)
      (((jointComparisonReindex η k).component j).val p) := hη (k.obj j) p

/-- 概要：制限した指定共同比較同型は元の指定同型の同じ内部前合成。
方針：順方向の Hom の制限の式を使う。
規約：全図式の同型の等式。使われ方：共同実現の添字制限の照合。 -/
lemma jointComparisonIso_reindex
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J K : Type u} [Category.{u} J] [Category.{u} K]
    {D E : KanEnrichedDiagram C J} (η : KanEnrichedDiagramComparison D E) (k : K ⥤ J)
    (hη : ∀ j (p : C), IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p)) :
    (jointComparisonReindex η k).jointComparisonIso
      (jointComparisonReindex_isQCatEquivalence η k hη) =
      diagramIsoCongr (jointEvaluation_reindex D k).symm (jointEvaluation_reindex E k).symm
        ((η.jointComparisonIso hη).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ⊗ₘ 𝟙 (SimplicialNerve C))) := by
  apply Iso.ext
  rw [diagramIsoCongr_hom, functorIsoPrecomp_hom]
  symm
  exact jointComparisonHom_reindex η k

end SerrePositivity.InfinityCategories.F2.Presentable
