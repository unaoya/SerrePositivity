module

public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramJointComparison
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedComparisonEdgeComposition

/-!
概要：共同 Kan 図式比較の合成を、元の比較辺を持つ三角形へ実現する。
方針：各共同単体の二つの対角比較に、既存の三点図式を適用する。
規約：成分だけでなく全添字・全対象を一つの三角形で扱う。
使われ方：P-12 の指定 straightening 底変換同型の合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：共同図式の二つの比較を同じ全パラメーターで合成する。
方針：各成分の豊穣比較を合成し、添字方向の自然性を順に使う。
規約：成分の合成は元の射の合成。使われ方：三角形の指定長辺。 -/
def jointComparisonTrans {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H) :
    KanEnrichedDiagramComparison D H where
  component j := (η.component j).trans (θ.component j)
  naturality f X := by
    change (D.map f).val X ≫ (η.component _).val X ≫ (θ.component _).val X =
      ((η.component _).val X ≫ (θ.component _).val X) ≫ (H.map f).val X
    rw [← Category.assoc, η.naturality, Category.assoc, θ.naturality, Category.assoc]

/-- 概要：共同合成の対角比較は、元の二つの対角比較の合成。
方針：成分の定義を展開する。規約：同じ対角を使う。
使われ方：共同三角形の長辺を元の比較へ同定する。 -/
lemma jointComparisonTrans_diagonal {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J I : Type u} [Category.{u} J] [LinearOrder I]
    {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H)
    (σ : I ⥤ J) (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    (jointComparisonTrans η θ).diagonalKanComparison σ T =
      (η.diagonalKanComparison σ T).trans (θ.diagonalKanComparison σ T) := by
  rfl

/-- 概要：共同単体の対角比較を元の三点 Kan 図式へ写す。
方針：既存の豊穣比較三角形を二つの対角比較へ適用する。
規約：三辺の成分を選び直さない。使われ方：共同三角形の全次数の定義。 -/
def jointComparisonDiagonalTriangle
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J I : Type u} [Category.{u} J] [LinearOrder I]
    {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H)
    (σ : I ⥤ J) (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    EnrichedFunctor SSet.{u} (SimplicialThickening I) (KanDiagramObject (ULift.{u} (Fin 3))) :=
  (kanEnrichedComparisonTriangle (η.diagonalKanComparison σ T)
    (θ.diagonalKanComparison σ T)).toEnrichedFunctor

/-- 概要：図式対象の等式で移送しても高次自然変換の各成分は異種等式で保持される。
方針：二つの対象等式を消去し恒等写像を計算する。
規約：元の高次変換を保持する。使われ方：共同三角形の対象移送の除去。 -/
lemma diagramHomTransport_component_heq {J : Type u} [Category.{u} J]
    {F G F' G' : KanDiagramObject J} (hF : F = F') (hG : G = G')
    {n : SimplexCategoryᵒᵖ} (x : (SimplicialCategory.sHom F G).obj n) (j : J) :
    HEq (((eqToHom (congrArg₂ (fun U V : KanDiagramObject J ↦
      SimplicialCategory.sHom U V) hF hG)).app n x).val j) (x.val j) := by
  subst F' G'
  rfl

/-- 概要：共同三点図式は全ての同時再添字付けと厳密に両立する。
方針：三成分の対角 Hom の再添字付けをそれぞれ計算する。
規約：面と退化の両方を含む。使われ方：共同三角形の単体的自然性。 -/
lemma jointComparisonDiagonalTriangle_reindex
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J I K : Type u} [Category.{u} J] [LinearOrder I] [LinearOrder K]
    {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H)
    (α : I →o K) (σ : K ⥤ J)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening K) C) :
    (SimplicialThickening.functor α).comp SSet
        (jointComparisonDiagonalTriangle η θ σ T) =
      jointComparisonDiagonalTriangle η θ (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet T) := by
  have hobj (i : SimplicialThickening I) :
      ((SimplicialThickening.functor α).comp SSet
        (jointComparisonDiagonalTriangle η θ σ T)).obj i =
      (jointComparisonDiagonalTriangle η θ (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet T)).obj i := by
    apply Subtype.ext
    apply CategoryTheory.Functor.ext
    · intro s t f
      rcases s with ⟨s⟩
      rcases t with ⟨t⟩
      fin_cases s <;> fin_cases t
      all_goals first
        | (have h := leOfHom f; norm_num at h; done)
        | (simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
    · intro s
      rcases s with ⟨s⟩
      fin_cases s <;> rfl
  refine EnrichedFunctor.ext SSet hobj ?_
  intro i j
  try simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  apply Subtype.ext
  funext t
  apply eq_of_heq
  refine (diagramHomTransport_component_heq (hobj i) (hobj j)
    ((((SimplicialThickening.functor α).comp SSet
      (jointComparisonDiagonalTriangle η θ σ T)).map i j).app n P) t).trans ?_
  rcases t with ⟨t⟩
  fin_cases t
  all_goals apply heq_of_eq
  all_goals
    have hij := SimplicialThickening.Path.le (P.obj 0)
  · let F := T.comp SSet D.toEnrichedFunctor
    change (((SimplicialThickening.functor α).map i j ≫
      diagonalKanDiagramHom σ F ((SimplicialThickening.functor α).obj i)
        ((SimplicialThickening.functor α).obj j)).app n) P =
      (diagonalKanDiagramHom (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet F) i j).app n P
    erw [diagonalKanDiagramHom_of_le σ F _ _ (α.monotone hij),
      diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl
  · let F := T.comp SSet E.toEnrichedFunctor
    change (((SimplicialThickening.functor α).map i j ≫
      diagonalKanDiagramHom σ F ((SimplicialThickening.functor α).obj i)
        ((SimplicialThickening.functor α).obj j)).app n) P =
      (diagonalKanDiagramHom (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet F) i j).app n P
    erw [diagonalKanDiagramHom_of_le σ F _ _ (α.monotone hij),
      diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl
  · let F := T.comp SSet H.toEnrichedFunctor
    change (((SimplicialThickening.functor α).map i j ≫
      diagonalKanDiagramHom σ F ((SimplicialThickening.functor α).obj i)
        ((SimplicialThickening.functor α).obj j)).app n) P =
      (diagonalKanDiagramHom (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet F) i j).app n P
    erw [diagonalKanDiagramHom_of_le σ F _ _ (α.monotone hij),
      diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl

/-- 概要：二つの共同比較を一つの三点図式の共同単体として束ねる。
方針：各共同単体の対角三角形と同時再添字付けの式を使う。
規約：始域の全単体を保持する。使われ方：指定比較辺の合成三角形。 -/
def jointComparisonTriangleArrow
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ SimplicialNerve C ⟶
      KanDiagramNerve (ULift.{u} (Fin 3)) where
  app _ := ↾fun s ↦ jointComparisonDiagonalTriangle η θ (kanDiagramSimplexBase s.1.down) s.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, T⟩
    exact (jointComparisonDiagonalTriangle_reindex η θ α.unop.toOrderHom.uliftMap
      (kanDiagramSimplexBase σ.down) T).symm

/-- 概要：共同比較の三角形を空間値の一つの三点関手族へ実現する。
方針：元の三点 Kan 図式の共同実現を合成する。
規約：全添字・全対象を同時に扱う。使われ方：三辺を指定辺へ戻す。 -/
def jointComparisonTriangleFamily
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⊗ SimplicialNerve C ⟶
      SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (ULift.{u} (Fin 3)))) :=
  jointComparisonTriangleArrow η θ ≫ kanDiagramRealization _

/-- 概要：豊穣恒等関手での前合成は元の全豊穣関手と一致する。
方針：対象を固定し Hom の恒等合成を除く。
規約：元の全 Hom 作用を保持する。使われ方：対角三角形の面の表示の正規化。 -/
lemma enrichedFunctor_id_comp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {L : Type (u + 1)} [Category.{u} L] [SimplicialCategory L]
    (F : EnrichedFunctor SSet.{u} C L) :
    (EnrichedFunctor.id SSet.{u} C).comp SSet F = F := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [EnrichedFunctor.comp, EnrichedFunctor.id, Category.id_comp,
    eqToHom_refl, Category.comp_id]

/-- 概要：共同三角形の最初の面は元の共同比較族。
方針：uncurry 後の同時対角評価を既存の三角形の面へ戻す。
規約：元の全単体の厳密な等式。使われ方：指定比較辺の初辺の回収。 -/
lemma jointComparisonTriangleFamily_first
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H) :
    jointComparisonTriangleFamily η θ ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap kanEnrichedComparisonFirstIndex))).app SpaceInfinity.{u} =
      η.jointComparisonFamily := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [jointComparisonTriangleFamily, KanEnrichedDiagramComparison.jointComparisonFamily,
    uncurry_natural_left, kanDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, ⟨τ, T⟩⟩
  change diagonalKanDiagramEvaluation
      (kanDiagramSimplexBase σ.down ⋙ kanEnrichedComparisonFirstIndex)
      (jointComparisonDiagonalTriangle η θ (kanDiagramSimplexBase τ.down) T) =
    diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ.down)
      (η.diagonalArrow (kanDiagramSimplexBase τ.down) T)
  simpa only [enrichedFunctor_id_comp, jointComparisonDiagonalTriangle,
    KanEnrichedDiagramComparison.diagonalArrow] using
    (kanEnrichedComparisonTriangle_first_diagonal
      (η.diagonalKanComparison (kanDiagramSimplexBase τ.down) T)
      (θ.diagonalKanComparison (kanDiagramSimplexBase τ.down) T)
      (kanDiagramSimplexBase σ.down) (EnrichedFunctor.id SSet _))

/-- 概要：共同三角形の後半の面は元の共同比較族。
方針：uncurry 後の同時対角評価を既存の三角形の面へ戻す。
規約：元の全単体の厳密な等式。使われ方：指定比較辺の後辺の回収。 -/
lemma jointComparisonTriangleFamily_second
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H) :
    jointComparisonTriangleFamily η θ ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap kanEnrichedComparisonSecondIndex))).app SpaceInfinity.{u} =
      θ.jointComparisonFamily := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [jointComparisonTriangleFamily, KanEnrichedDiagramComparison.jointComparisonFamily,
    uncurry_natural_left, kanDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, ⟨τ, T⟩⟩
  change diagonalKanDiagramEvaluation
      (kanDiagramSimplexBase σ.down ⋙ kanEnrichedComparisonSecondIndex)
      (jointComparisonDiagonalTriangle η θ (kanDiagramSimplexBase τ.down) T) =
    diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ.down)
      (θ.diagonalArrow (kanDiagramSimplexBase τ.down) T)
  simpa only [enrichedFunctor_id_comp, jointComparisonDiagonalTriangle,
    KanEnrichedDiagramComparison.diagonalArrow] using
    (kanEnrichedComparisonTriangle_second_diagonal
      (η.diagonalKanComparison (kanDiagramSimplexBase τ.down) T)
      (θ.diagonalKanComparison (kanDiagramSimplexBase τ.down) T)
      (kanDiagramSimplexBase σ.down) (EnrichedFunctor.id SSet _))

/-- 概要：共同三角形の長辺の面は元の共同比較族。
方針：uncurry 後の同時対角評価を既存の三角形の面へ戻す。
規約：元の全単体の厳密な等式。使われ方：指定比較辺の合成した長辺の回収。 -/
lemma jointComparisonTriangleFamily_long
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H) :
    jointComparisonTriangleFamily η θ ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap kanEnrichedComparisonLongIndex))).app SpaceInfinity.{u} =
      (jointComparisonTrans η θ).jointComparisonFamily := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [jointComparisonTriangleFamily, KanEnrichedDiagramComparison.jointComparisonFamily,
    uncurry_natural_left, kanDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, ⟨τ, T⟩⟩
  change diagonalKanDiagramEvaluation
      (kanDiagramSimplexBase σ.down ⋙ kanEnrichedComparisonLongIndex)
      (jointComparisonDiagonalTriangle η θ (kanDiagramSimplexBase τ.down) T) =
    diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ.down)
      ((jointComparisonTrans η θ).diagonalArrow (kanDiagramSimplexBase τ.down) T)
  simpa only [enrichedFunctor_id_comp, jointComparisonDiagonalTriangle,
    KanEnrichedDiagramComparison.diagonalArrow, jointComparisonTrans_diagonal] using
    (kanEnrichedComparisonTriangle_long_diagonal
      (η.diagonalKanComparison (kanDiagramSimplexBase τ.down) T)
      (θ.diagonalKanComparison (kanDiagramSimplexBase τ.down) T)
      (kanDiagramSimplexBase σ.down) (EnrichedFunctor.id SSet _))

/-- 概要：元の共同比較の三辺は一つの合成三角形を持つ。
方針：共同三点族を転置し、既存の添字三角形の三辺を回収する。
規約：元の比較辺を保持する。使われ方：共同比較の合成の Hom 等式。 -/
def jointComparisonEdge_compStruct
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H) :
    SSet.Edge.CompStruct η.jointComparisonEdge θ.jointComparisonEdge
      (jointComparisonTrans η θ).jointComparisonEdge := by
  let T := transposeFunctorFamily (jointComparisonTriangleFamily η θ)
  refine (kanEnrichedComparisonIndexTriangle.map T).ofEq ?_ ?_ ?_
  · change (((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap kanEnrichedComparisonFirstIndex) ≫
        transposeFunctorFamily (jointComparisonTriangleFamily η θ)).app
          (Opposite.op ⦋1⦌)) coherentResolutionComparisonIndexEdge.edge =
      (transposeFunctorFamily η.jointComparisonFamily).app
        (Opposite.op ⦋1⦌) coherentResolutionComparisonIndexEdge.edge
    rw [← transposeFunctorFamily_pre, jointComparisonTriangleFamily_first]
  · change (((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap kanEnrichedComparisonSecondIndex) ≫
        transposeFunctorFamily (jointComparisonTriangleFamily η θ)).app
          (Opposite.op ⦋1⦌)) coherentResolutionComparisonIndexEdge.edge =
      (transposeFunctorFamily θ.jointComparisonFamily).app
        (Opposite.op ⦋1⦌) coherentResolutionComparisonIndexEdge.edge
    rw [← transposeFunctorFamily_pre, jointComparisonTriangleFamily_second]
  · change (((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap kanEnrichedComparisonLongIndex) ≫
        transposeFunctorFamily (jointComparisonTriangleFamily η θ)).app
          (Opposite.op ⦋1⦌)) coherentResolutionComparisonIndexEdge.edge =
      (transposeFunctorFamily (jointComparisonTrans η θ).jointComparisonFamily).app
        (Opposite.op ⦋1⦌) coherentResolutionComparisonIndexEdge.edge
    rw [← transposeFunctorFamily_pre, jointComparisonTriangleFamily_long]

/-- 概要：共同比較の実現は全図式間の Hom として合成を保存する。
方針：指定された三辺の合成三角形のホモトピー圏の関係を使う。
規約：値ごとの一致から全自然変換の一致を推論しない。
使われ方：P-12 の共同切断の指定底変換比較の合成計算。 -/
lemma jointComparisonEdge_hom_trans
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E H : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E H) :
    SSet.Truncated.HomotopyCategory.homMk η.jointComparisonEdge ≫
      SSet.Truncated.HomotopyCategory.homMk θ.jointComparisonEdge =
    SSet.Truncated.HomotopyCategory.homMk (jointComparisonTrans η θ).jointComparisonEdge :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (jointComparisonEdge_compStruct η θ).toTruncated

end SerrePositivity.InfinityCategories.F2.Presentable
