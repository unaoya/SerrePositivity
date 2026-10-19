module

public import SerrePositivity.InfinityCategories.F1B.KanGlobalRelativeInitialFamily

/-!
概要：局所相対余錐から元の図式と標的の全図式を固定した大域図式を構成する。
方針：coherent な相対始対象の族を恒等射上の全単射で大域図式へ戻す。
規約：各 fiber の指定図式の相対余錐だけを要求する。
使われ方：関手の境界制限上の相対 Kan 拡張の存在。
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
lemma exists_kanGlobalRelative_diagram {K C P Q X : SSet.{u}}
    [Quasicategory C] [Quasicategory X] (p : K ⟶ C) [CocartesianFibration p]
    (v : P ⟶ Q) [Mono v] (F : K ⟶ (ihom Q).obj X)
    (H₀ : relativeJoin p (𝟙 C) ⟶ (ihom P).obj X)
    (hFU : F ≫ (pre v).app X = relativeJoinInl p (𝟙 C) ≫ H₀)
    (hlocal : ∀ c : C _⦋0⦌, ∃ z : JoinCocone (vertexFiberι p c ≫ F),
      KanRelativeCoconeLifting ((pre v).app X) z ∧
        z.val ≫ (pre v).app X = (kanRelativeJoinFiberCocone p c H₀).val) :
    ∃ H : relativeJoin p (𝟙 C) ⟶ (ihom Q).obj X,
      relativeJoinInl p (𝟙 C) ≫ H = F ∧ H ≫ (pre v).app X = H₀ ∧
        ∀ c : C _⦋0⦌, InitialBoundaryLifting
          (kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) ((pre v).app X))
          ((kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H).app
            (Opposite.op ⦋0⦌) c) := by
  obtain ⟨l, hl, hli⟩ := exists_kanGlobalRelative_initial_family p v F H₀ hFU hlocal
  have hlpre : l ≫ kanFiberwiseHomPre (D := (ihom Q).obj X) (kanRelativeJoinInlOver p) =
      kanGlobalDiagramFamily p F := by
    have h := congrArg (fun z ↦ z ≫ pullback.fst (kanFiberwiseHomPostcomp p ((pre v).app X))
      (kanFiberwiseHomPre (D := (ihom P).obj X) (kanRelativeJoinInlOver p))) hl
    simp only [Category.assoc] at h
    erw [kanFiberwiseRelativeRestriction_fst, kanGlobalRelativeDiagramFamily_fst] at h
    exact h
  have hlpost : l ≫ kanFiberwiseHomPostcomp (relativeJoinBaseProjection p (𝟙 C)) ((pre v).app X) =
      kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H₀ := by
    have h := congrArg (fun z ↦ z ≫ pullback.snd (kanFiberwiseHomPostcomp p ((pre v).app X))
      (kanFiberwiseHomPre (D := (ihom P).obj X) (kanRelativeJoinInlOver p))) hl
    simp only [Category.assoc] at h
    erw [kanFiberwiseRelativeRestriction_snd, kanGlobalRelativeDiagramFamily_snd] at h
    exact h
  have hlp : l ≫ kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) ((ihom Q).obj X) =
      𝟙 C := by
    change l ≫ kanFiberwiseHomProjection
      (Over.mk (relativeJoinBaseProjection p (𝟙 C))).hom ((ihom Q).obj X) = 𝟙 C
    rw [← kanFiberwiseHomPre_projection (D := (ihom Q).obj X) (kanRelativeJoinInlOver p),
      ← Category.assoc, hlpre]
    exact kanGlobalDiagramFamily_projection p F
  let H := (kanGlobalDiagramFamilyEquiv (D := (ihom Q).obj X)
    (relativeJoinBaseProjection p (𝟙 C))).symm ⟨l, hlp⟩
  have hH : kanGlobalDiagramFamily (relativeJoinBaseProjection p (𝟙 C)) H = l :=
    congrArg Subtype.val ((kanGlobalDiagramFamilyEquiv (D := (ihom Q).obj X)
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

end SerrePositivity.InfinityCategories.F1B
