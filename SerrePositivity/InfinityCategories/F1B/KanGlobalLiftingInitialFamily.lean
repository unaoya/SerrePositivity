module

public import SerrePositivity.InfinityCategories.F1B.KanGlobalRelativeCoconeVertex
public import SerrePositivity.InfinityCategories.F1B.KanGlobalRelativeDiagramFamily
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinLiftingCartesian
public import SerrePositivity.InfinityCategories.F1B.KanRelativeInitialPullback

/-!
概要：指定した大域図式の上の局所相対余錐から相対始対象の coherent な族を選ぶ。
方針：各頂点で二つの指定を保つ相対始対象を構成し、その全体からの射の切断を取る。
規約：標的の射は単射な圏論的同値に対する右持ち上げを持つ。
使われ方：一般の標的上の大域的な相対 Kan 図式の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：局所の相対余錐から指定された相対標的の頂点上に相対始対象を得る。
方針：fiber の同型で余錐を全空間へ送り、二つの像の式と局所から全空間への移送を使う。
規約：一つの指定された fiber の図式だけを仮定する。
使われ方：相対始対象の大域的な族の各頂点での存在。 -/
lemma exists_kanGlobalRelative_initial_vertex_of_lifting {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E] (p : K ⟶ C) [CocartesianFibration p]
    (U : D ⟶ E) (hU : KanEquivalenceLifting U) (F : K ⟶ D)
    (H₀ : relativeJoin p (𝟙 C) ⟶ E)
    (hFU : F ≫ U = relativeJoinInl p (𝟙 C) ≫ H₀) (c : C _⦋0⦌)
    (hlocal : ∃ z : JoinCocone (vertexFiberι p c ≫ F),
      IsRelativeColimitCone U z ∧
        z.val ≫ U = (kanRelativeJoinFiberCocone p c H₀).val) :
    ∃ x : (kanFiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D) _⦋0⦌,
      (kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U).app
          (Opposite.op ⦋0⦌) x =
        (kanGlobalRelativeDiagramFamily (kanRelativeJoinInlOver p) U F H₀ hFU).app
          (Opposite.op ⦋0⦌) c ∧
        InitialBoundaryLifting
          (kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U) x := by
  obtain ⟨z, hz, hzU⟩ := hlocal
  let x := ((kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
    (functorVertex z.val)).val
  refine ⟨x, ?_, kanRelativeJoinRelative_initialBoundary_of_relativeColimit p U hU c hz⟩
  have himages := kanGlobalRelativeCocone_vertex_images p U F H₀ c z hzU
  apply Types.ext_of_isPullback ((IsPullback.of_hasPullback
    (kanFiberwiseHomPostcomp p U)
    (kanFiberwiseHomPre (D := E) (kanRelativeJoinInlOver p))).map
      ((evaluation _ (Type u)).obj (Opposite.op ⦋0⦌)))
  · change (kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U ≫
        pullback.fst _ _).app (Opposite.op ⦋0⦌) x =
      (kanGlobalRelativeDiagramFamily (kanRelativeJoinInlOver p) U F H₀ hFU ≫
        pullback.fst _ _).app (Opposite.op ⦋0⦌) c
    erw [kanFiberwiseRelativeRestriction_fst, kanGlobalRelativeDiagramFamily_fst]
    exact himages.1
  · change (kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U ≫
        pullback.snd _ _).app (Opposite.op ⦋0⦌) x =
      (kanGlobalRelativeDiagramFamily (kanRelativeJoinInlOver p) U F H₀ hFU ≫
        pullback.snd _ _).app (Opposite.op ⦋0⦌) c
    erw [kanFiberwiseRelativeRestriction_snd, kanGlobalRelativeDiagramFamily_snd]
    exact himages.2

/-- 概要：各 fiber に指定された相対余錐が存在すれば大域的な相対始対象の族を選べる。
方針：各頂点での相対始対象の存在を一般の coherent な族の選択へ渡す。
規約：標的の全図式 H₀ と元の図式 F を同時に固定する。
使われ方：相対 join 上の実際の図式を作る際の族の入力。 -/
lemma exists_kanGlobalRelative_initial_family_of_lifting {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E] (p : K ⟶ C) [CocartesianFibration p]
    (U : D ⟶ E) (hU : KanEquivalenceLifting U) (F : K ⟶ D)
    (H₀ : relativeJoin p (𝟙 C) ⟶ E)
    (hFU : F ≫ U = relativeJoinInl p (𝟙 C) ≫ H₀)
    (hlocal : ∀ c : C _⦋0⦌, ∃ z : JoinCocone (vertexFiberι p c ≫ F),
      IsRelativeColimitCone U z ∧
        z.val ≫ U = (kanRelativeJoinFiberCocone p c H₀).val) :
    ∃ l : C ⟶ kanFiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D,
      l ≫ kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U =
        kanGlobalRelativeDiagramFamily (kanRelativeJoinInlOver p) U F H₀ hFU ∧
      ∀ c : C _⦋0⦌, InitialBoundaryLifting
        (kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U)
        (l.app (Opposite.op ⦋0⦌) c) :=
  exists_kanRelativeInitial_family_of_vertices _ _
    (fun c ↦ exists_kanGlobalRelative_initial_vertex_of_lifting p U hU F H₀ hFU c (hlocal c))

end SerrePositivity.InfinityCategories.F1B
