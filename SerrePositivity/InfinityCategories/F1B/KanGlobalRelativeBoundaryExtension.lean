module

public import SerrePositivity.InfinityCategories.F1B.KanBoundaryRelativeColimitExistence
public import SerrePositivity.InfinityCategories.F1B.KanGlobalLiftingDiagram
public import SerrePositivity.InfinityCategories.F1B.KanRelativeColimitTrivialComparison

/-!
概要：標的の全図式も指定した相対 join 図式の境界延長。
方針：相対内部 Hom 上の局所相対余極限を境界の最初の頂点から供給して組み立てる。
規約：境界、元の図式、標的図式の三つを厳密に固定する。
使われ方：相対 Kan 図式からの写像空間の制限の境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：最初の境界頂点の局所 U 余極限から標的も固定した境界延長を構成する。
方針：各 fiber の余錐の族を相対内部 Hom に転置し、標準相対余極限の組み立てを適用する。
規約：U は単射な圏論的同値の右持ち上げを持つ。境界の他の頂点に普遍性は不要。
使われ方：関手の相対制限の始点境界充填への大域的な入力。 -/
lemma exists_kanGlobalRelativeBoundary_diagram_extension {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E) (hU : KanEquivalenceLifting U)
    (n : ℕ) (sj : internalHom.PullbackObjObj (boundary (n + 1)).ι U)
    (F : K ⟶ (ihom (Δ[n + 1] : SSet.{u})).obj D)
    (A : relativeJoin p (𝟙 C) ⟶ (ihom (boundary (n + 1) : SSet.{u})).obj D)
    (G : relativeJoin p (𝟙 C) ⟶ (ihom (Δ[n + 1] : SSet.{u})).obj E)
    (hFA : F ≫ (pre (boundary (n + 1)).ι).app D = relativeJoinInl p (𝟙 C) ≫ A)
    (hFG : F ≫ (ihom (Δ[n + 1] : SSet.{u})).map U = relativeJoinInl p (𝟙 C) ≫ G)
    (hAG : A ≫ (ihom (boundary (n + 1) : SSet.{u})).map U =
      G ≫ (pre (boundary (n + 1)).ι).app E)
    (hfirst : ∀ c : C _⦋0⦌, IsRelativeColimitCone U (kanCoconeFamilyAt
      (kanFunctorTranspose (kanRelativeJoinFiberCocone p c A).val)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩)) :
    ∃ H : relativeJoin p (𝟙 C) ⟶ (ihom (Δ[n + 1] : SSet.{u})).obj D,
      relativeJoinInl p (𝟙 C) ≫ H = F ∧
        H ≫ (pre (boundary (n + 1)).ι).app D = A ∧
          H ≫ (ihom (Δ[n + 1] : SSet.{u})).map U = G := by
  have : InnerFibration U := hU.innerFibration
  have : Quasicategory ((internalHom.obj (Opposite.op (Δ[n + 1] : SSet.{u}))).obj D) :=
    inferInstanceAs (Quasicategory ((ihom (Δ[n + 1] : SSet.{u})).obj D))
  have : Quasicategory sj.pt := kanRelativeInternalHomTarget_quasicategory U _ sj
  have hsj : KanEquivalenceLifting sj.π := by
    intro X Y i hm hi
    exact KanEquivalenceLifting.relativeInternalHom hU _ sj i hm hi
  let H₀ := sj.isPullback.lift A G hAG
  have h₀A : H₀ ≫ sj.fst = A := sj.isPullback.lift_fst _ _ _
  have h₀G : H₀ ≫ sj.snd = G := sj.isPullback.lift_snd _ _ _
  have hFH₀ : F ≫ sj.π = relativeJoinInl p (𝟙 C) ≫ H₀ := by
    apply sj.hom_ext
    · rw [Category.assoc, sj.π_fst, Category.assoc, h₀A]
      exact hFA
    · rw [Category.assoc, sj.π_snd, Category.assoc, h₀G]
      exact hFG
  have hlocal : ∀ c : C _⦋0⦌, ∃ z : JoinCocone (vertexFiberι p c ≫ F),
      IsRelativeColimitCone sj.π z ∧ z.val ≫ sj.π = (kanRelativeJoinFiberCocone p c H₀).val := by
    intro c
    let j : join (vertexFiber p c) (Δ[0] : SSet.{u}) ⟶ relativeJoin p (𝟙 C) :=
      (kanRelativeJoinBaseFiberIso p c).hom ≫
        vertexFiberι (relativeJoinBaseProjection p (𝟙 C)) c
    let a := kanFunctorTranspose (kanRelativeJoinFiberCocone p c A).val
    let d := kanFunctorTranspose (vertexFiberι p c ≫ F)
    let g := kanFunctorTranspose (kanRelativeJoinFiberCocone p c G).val
    have hwA : joinInl (vertexFiber p c) (Δ[0] : SSet.{u}) ≫
        (kanRelativeJoinFiberCocone p c A).val =
          (vertexFiberι p c ≫ F) ≫ (pre (boundary (n + 1)).ι).app D := by
      rw [(kanRelativeJoinFiberCocone p c A).property, Category.assoc,
        ← hFA, ← Category.assoc]
    have hwG : joinInl (vertexFiber p c) (Δ[0] : SSet.{u}) ≫
        (kanRelativeJoinFiberCocone p c G).val =
          (vertexFiberι p c ≫ F) ≫ (ihom (Δ[n + 1] : SSet.{u})).map U := by
      rw [(kanRelativeJoinFiberCocone p c G).property, Category.assoc,
        ← hFG, ← Category.assoc]
    have ha : a ≫ coconeRestriction (vertexFiber p c) D = (boundary (n + 1)).ι ≫ d := by
      change kanFunctorTranspose (kanRelativeJoinFiberCocone p c A).val ≫
        (pre (joinInl (vertexFiber p c) (Δ[0] : SSet.{u}))).app D =
          (boundary (n + 1)).ι ≫ kanFunctorTranspose (vertexFiberι p c ≫ F)
      rw [← kanFunctorTranspose_pre_left, hwA, kanFunctorTranspose_pre_right]
    have hg : d ≫ (ihom (vertexFiber p c)).map U =
        g ≫ coconeRestriction (vertexFiber p c) E := by
      change kanFunctorTranspose (vertexFiberι p c ≫ F) ≫ (ihom (vertexFiber p c)).map U =
        kanFunctorTranspose (kanRelativeJoinFiberCocone p c G).val ≫
          (pre (joinInl (vertexFiber p c) (Δ[0] : SSet.{u}))).app E
      rw [← kanFunctorTranspose_postcomp, ← kanFunctorTranspose_pre_left, hwG]
    have hga : a ≫ (ihom (join (vertexFiber p c) (Δ[0] : SSet.{u}))).map U =
        (boundary (n + 1)).ι ≫ g := by
      have hraw : (kanRelativeJoinFiberCocone p c A).val ≫
          (ihom (boundary (n + 1) : SSet.{u})).map U =
        (kanRelativeJoinFiberCocone p c G).val ≫ (pre (boundary (n + 1)).ι).app E := by
        change (j ≫ A) ≫ (ihom (boundary (n + 1) : SSet.{u})).map U =
          (j ≫ G) ≫ (pre (boundary (n + 1)).ι).app E
        simp only [Category.assoc]
        rw [hAG]
      have ht := congrArg kanFunctorTranspose hraw
      rw [kanFunctorTranspose_postcomp, kanFunctorTranspose_pre_right] at ht
      exact ht
    obtain ⟨z, hz, hzA, hzG⟩ :=
      exists_kanBoundaryRelativeColimit_of_first_relativeColimit U n sj a d g hg ha hga (hfirst c)
    have hbase : kanFunctorTranspose d = vertexFiberι p c ≫ F :=
      kanFunctorTranspose_transpose _
    let z' : JoinCocone (vertexFiberι p c ≫ F) := ⟨z.val, z.property.trans hbase⟩
    refine ⟨z', (kanIsRelativeColimitCone_congr sj.π hbase z z' rfl).1 hz, ?_⟩
    apply sj.hom_ext
    · rw [Category.assoc, sj.π_fst]
      change z.val ≫ (pre (boundary (n + 1)).ι).app D =
        (kanRelativeJoinFiberCocone p c H₀).val ≫ sj.fst
      rw [hzA]
      change kanFunctorTranspose a = j ≫ H₀ ≫ sj.fst
      rw [h₀A]
      exact kanFunctorTranspose_transpose _
    · rw [Category.assoc, sj.π_snd]
      change z.val ≫ (ihom (Δ[n + 1] : SSet.{u})).map U =
        (kanRelativeJoinFiberCocone p c H₀).val ≫ sj.snd
      rw [hzG]
      change kanFunctorTranspose g = j ≫ H₀ ≫ sj.snd
      rw [h₀G]
      exact kanFunctorTranspose_transpose _
  obtain ⟨H, hHF, hH₀, _⟩ :=
    exists_kanGlobalRelative_diagram_with_relative_colimits_of_lifting p sj.π hsj F H₀ hFH₀ hlocal
  refine ⟨H, hHF, ?_, ?_⟩
  · have h := congrArg (fun f ↦ f ≫ sj.fst) hH₀
    rw [Category.assoc, sj.π_fst, h₀A] at h
    exact h
  · have h := congrArg (fun f ↦ f ≫ sj.snd) hH₀
    rw [Category.assoc, sj.π_snd, h₀G] at h
    exact h

end SerrePositivity.InfinityCategories.F1B
