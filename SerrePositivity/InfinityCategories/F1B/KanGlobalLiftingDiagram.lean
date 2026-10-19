module

public import SerrePositivity.InfinityCategories.F1B.KanGlobalLiftingInitialFamily
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinFiberRelativeCocone

/-!
概要：局所相対余錐から元の図式と標的の全図式を固定した大域図式を構成する。
方針：coherent な相対始対象の族を恒等射上の全単射で大域図式へ戻す。
規約：各 fiber の指定図式の相対余錐だけを要求する。
使われ方：一般の標的上の標準局所余極限からの相対 Kan 拡張の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：各 fiber の局所相対余錐から指定された標的の全図式上の大域的な図式が存在する。
方針：相対始対象の族の二成分を回収し、底への射影を固定して大域図式へ戻す。
規約：元の図式と標的の全図式は厳密に保ち、各点の全空間での相対充填性も得る。
使われ方：写像空間の制限定理の境界固定の Kan 拡張の構成。 -/
lemma exists_kanGlobalRelative_diagram_of_lifting {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E] (p : K ⟶ C) [CocartesianFibration p]
    (U : D ⟶ E) (hU : KanEquivalenceLifting U) (F : K ⟶ D)
    (H₀ : relativeJoin p (𝟙 C) ⟶ E)
    (hFU : F ≫ U = relativeJoinInl p (𝟙 C) ≫ H₀)
    (hlocal : ∀ c : C _⦋0⦌, ∃ z : JoinCocone (vertexFiberι p c ≫ F),
      IsRelativeColimitCone U z ∧
        z.val ≫ U = (kanRelativeJoinFiberCocone p c H₀).val) :
    ∃ H : relativeJoin p (𝟙 C) ⟶ D,
      relativeJoinInl p (𝟙 C) ≫ H = F ∧ H ≫ U = H₀ ∧
        ∀ c : C _⦋0⦌, InitialBoundaryLifting
          (kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U)
          ((kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H).app
            (Opposite.op ⦋0⦌) c) := by
  obtain ⟨l, hl, hli⟩ := exists_kanGlobalRelative_initial_family_of_lifting p U hU F H₀ hFU hlocal
  have hlpre : l ≫ kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p) =
      kanGlobalDiagramFamily p F := by
    have h := congrArg (fun z ↦ z ≫ pullback.fst (kanFiberwiseHomPostcomp p U)
      (kanFiberwiseHomPre (D := E) (kanRelativeJoinInlOver p))) hl
    simp only [Category.assoc] at h
    erw [kanFiberwiseRelativeRestriction_fst, kanGlobalRelativeDiagramFamily_fst] at h
    exact h
  have hlpost : l ≫ kanFiberwiseHomPostcomp (relativeJoinBaseProjection p (𝟙 C)) U =
      kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H₀ := by
    have h := congrArg (fun z ↦ z ≫ pullback.snd (kanFiberwiseHomPostcomp p U)
      (kanFiberwiseHomPre (D := E) (kanRelativeJoinInlOver p))) hl
    simp only [Category.assoc] at h
    erw [kanFiberwiseRelativeRestriction_snd, kanGlobalRelativeDiagramFamily_snd] at h
    exact h
  have hlp : l ≫ kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D =
      𝟙 C := by
    change l ≫ kanFiberwiseHomProjection
      (Over.mk (relativeJoinBaseProjection p (𝟙 C))).hom D = 𝟙 C
    rw [← kanFiberwiseHomPre_projection (D := D) (kanRelativeJoinInlOver p),
      ← Category.assoc, hlpre]
    exact kanGlobalDiagramFamily_projection p F
  let H := (kanGlobalDiagramFamilyEquiv (D := D)
    (relativeJoinBaseProjection p (𝟙 C))).symm ⟨l, hlp⟩
  have hH : kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H = l :=
    congrArg Subtype.val ((kanGlobalDiagramFamilyEquiv (D := D)
      (relativeJoinBaseProjection p (𝟙 C))).apply_symm_apply ⟨l, hlp⟩)
  refine ⟨H, ?_, ?_, ?_⟩
  · apply kanGlobalDiagramFamily_injective p
    erw [← kanGlobalDiagramFamily_pre (kanRelativeJoinInlOver p) H, hH]
    exact hlpre
  · apply kanGlobalDiagramFamily_injective (relativeJoinBaseProjection p (𝟙 C))
    rw [kanGlobalDiagramFamily_postcomp, hH]
    exact hlpost
  · rw [hH]
    exact hli


/-- 概要：局所の標準 U 余極限から全 fiber で標準的に相対普遍な大域図式を構成する。
方針：大域図式の全空間での充填性を各 fiber へ制限し、標準の相対余極限条件へ戻す。
規約：元の図式と標的の全図式を厳密に保つ。
使われ方：一般の右持ち上げ条件を持つ標的上の相対 Kan 図式の存在。 -/
lemma exists_kanGlobalRelative_diagram_with_relative_colimits_of_lifting
    {K C D E : SSet.{u}} [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E) (hU : KanEquivalenceLifting U)
    (F : K ⟶ D) (H₀ : relativeJoin p (𝟙 C) ⟶ E)
    (hFU : F ≫ U = relativeJoinInl p (𝟙 C) ≫ H₀)
    (hlocal : ∀ c : C _⦋0⦌, ∃ z : JoinCocone (vertexFiberι p c ≫ F),
      IsRelativeColimitCone U z ∧ z.val ≫ U = (kanRelativeJoinFiberCocone p c H₀).val) :
    ∃ H : relativeJoin p (𝟙 C) ⟶ D,
      relativeJoinInl p (𝟙 C) ≫ H = F ∧ H ≫ U = H₀ ∧
        ∀ c : C _⦋0⦌, IsRelativeColimitCone U (kanRelativeJoinFiberCocone p c H) := by
  obtain ⟨H, hF, hH₀, hHi⟩ := exists_kanGlobalRelative_diagram_of_lifting p U hU F H₀ hFU hlocal
  exact ⟨H, hF, hH₀, fun c ↦ kanIsRelativeColimitCone_of_lifting U _
    (kanRelativeJoinFiberCocone_relative_of_initialBoundary p U c H (hHi c))⟩

end SerrePositivity.InfinityCategories.F1B
