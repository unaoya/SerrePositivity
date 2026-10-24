module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftCanonicalExistence
public import SerrePositivity.InfinityCategories.F1B.KanExtension.GlobalRelativeBoundaryExtension

/-!
概要：標準局所条件から元の関手圏上で元・境界・標的を保つ左 Kan 延長を構成する。
方針：境界固定の局所相対余極限を相対内部 Hom に作り、元の図式の厳密な存在を使う。
規約：境界の最初の頂点の局所 U 余極限性だけを仮定する。
使われ方：元の相対左 Kan 制限の始点境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：境界の最初の局所普遍性から元と底を同時に固定する大域境界延長が存在する。
方針：局所の境界充填を相対内部 Hom の標準余極限とし、厳密な左 Kan 存在へ渡す。
規約：δ は充満忠実な inner 単射。相手の境界頂点に普遍性は不要。
使われ方：元の相対制限から出る写像空間の比較の充填。 -/
lemma exists_kanRelativeLeftBoundary_diagram_extension {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (n : ℕ) (sj : internalHom.PullbackObjObj (boundary (n + 1)).ι U)
    (F : K ⟶ (ihom (Δ[n + 1] : SSet.{u})).obj D)
    (A : C ⟶ (ihom (boundary (n + 1) : SSet.{u})).obj D)
    (G : C ⟶ (ihom (Δ[n + 1] : SSet.{u})).obj E)
    (hFA : F ≫ (pre (boundary (n + 1)).ι).app D = δ ≫ A)
    (hFG : F ≫ (ihom (Δ[n + 1] : SSet.{u})).map U = δ ≫ G)
    (hAG : A ≫ (ihom (boundary (n + 1) : SSet.{u})).map U =
      G ≫ (pre (boundary (n + 1)).ι).app E)
    (hfirst : ∀ c : C _⦋0⦌, IsRelativeColimitCone U (kanCoconeFamilyAt
      (SerrePositivity.InfinityCategories.F1B.functorTranspose (leftKanCanonicalCocone δ A c).val)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩)) :
    ∃ H : C ⟶ (ihom (Δ[n + 1] : SSet.{u})).obj D, δ ≫ H = F ∧
      H ≫ (pre (boundary (n + 1)).ι).app D = A ∧
        H ≫ (ihom (Δ[n + 1] : SSet.{u})).map U = G := by
  have : InnerFibration U := hU.innerFibration
  have : Quasicategory ((internalHom.obj (Opposite.op (Δ[n + 1] : SSet.{u}))).obj D) :=
    inferInstanceAs (Quasicategory ((ihom (Δ[n + 1] : SSet.{u})).obj D))
  have : Quasicategory sj.pt := kanRelativeInternalHomTarget_quasicategory U _ sj
  have hsj : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting sj.π := by
    intro X Y i hm hi
    exact SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.relativeInternalHom hU _ sj i hm hi
  let H₀ := sj.isPullback.lift A G hAG
  have h₀A : H₀ ≫ sj.fst = A := sj.isPullback.lift_fst _ _ _
  have h₀G : H₀ ≫ sj.snd = G := sj.isPullback.lift_snd _ _ _
  have hFH₀ : F ≫ sj.π = δ ≫ H₀ := by
    apply sj.hom_ext
    · rw [Category.assoc, sj.π_fst, Category.assoc, h₀A]
      exact hFA
    · rw [Category.assoc, sj.π_snd, Category.assoc, h₀G]
      exact hFG
  have hlocal : ∀ c : C _⦋0⦌, ∃ z : JoinCocone (leftKanDiagram δ F c),
      IsRelativeColimitCone sj.π z ∧ z.val ≫ sj.π = (leftKanCanonicalCocone δ H₀ c).val := by
    intro c
    let j := kanLeftCanonicalCoconeMap δ c
    let a := SerrePositivity.InfinityCategories.F1B.functorTranspose (leftKanCanonicalCocone δ A c).val
    let d := SerrePositivity.InfinityCategories.F1B.functorTranspose (leftKanDiagram δ F c)
    let g := SerrePositivity.InfinityCategories.F1B.functorTranspose (leftKanCanonicalCocone δ G c).val
    have hwA : joinInl (leftKanShape δ c) (Δ[0] : SSet.{u}) ≫
        (leftKanCanonicalCocone δ A c).val =
          (leftKanDiagram δ F c) ≫ (pre (boundary (n + 1)).ι).app D := by
      rw [(leftKanCanonicalCocone δ A c).property]
      simp only [leftKanDiagram, Category.assoc, hFA]
    have hwG : joinInl (leftKanShape δ c) (Δ[0] : SSet.{u}) ≫
        (leftKanCanonicalCocone δ G c).val =
          (leftKanDiagram δ F c) ≫ (ihom (Δ[n + 1] : SSet.{u})).map U := by
      rw [(leftKanCanonicalCocone δ G c).property]
      simp only [leftKanDiagram, Category.assoc, hFG]
    have ha : a ≫ coconeRestriction (leftKanShape δ c) D = (boundary (n + 1)).ι ≫ d := by
      change SerrePositivity.InfinityCategories.F1B.functorTranspose (leftKanCanonicalCocone δ A c).val ≫
        (pre (joinInl (leftKanShape δ c) (Δ[0] : SSet.{u}))).app D =
          (boundary (n + 1)).ι ≫ SerrePositivity.InfinityCategories.F1B.functorTranspose (leftKanDiagram δ F c)
      rw [← SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left, hwA, SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_right]
    have hg : d ≫ (ihom (leftKanShape δ c)).map U =
        g ≫ coconeRestriction (leftKanShape δ c) E := by
      change SerrePositivity.InfinityCategories.F1B.functorTranspose (leftKanDiagram δ F c) ≫ (ihom (leftKanShape δ c)).map U =
        SerrePositivity.InfinityCategories.F1B.functorTranspose (leftKanCanonicalCocone δ G c).val ≫
          (pre (joinInl (leftKanShape δ c) (Δ[0] : SSet.{u}))).app E
      rw [← kanFunctorTranspose_postcomp, ← SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left, hwG]
    have hga : a ≫ (ihom (join (leftKanShape δ c) (Δ[0] : SSet.{u}))).map U =
        (boundary (n + 1)).ι ≫ g := by
      have hraw : (leftKanCanonicalCocone δ A c).val ≫
          (ihom (boundary (n + 1) : SSet.{u})).map U =
        (leftKanCanonicalCocone δ G c).val ≫ (pre (boundary (n + 1)).ι).app E := by
        change (j ≫ A) ≫ (ihom (boundary (n + 1) : SSet.{u})).map U =
          (j ≫ G) ≫ (pre (boundary (n + 1)).ι).app E
        simp only [Category.assoc]
        rw [hAG]
      have ht := congrArg SerrePositivity.InfinityCategories.F1B.functorTranspose hraw
      rw [kanFunctorTranspose_postcomp, SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_right] at ht
      exact ht
    obtain ⟨z, hz, hzA, hzG⟩ :=
      exists_kanBoundaryRelativeColimit_of_first_relativeColimit U n sj a d g hg ha hga (hfirst c)
    have hbase : SerrePositivity.InfinityCategories.F1B.functorTranspose d = leftKanDiagram δ F c :=
      SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose _
    let z' : JoinCocone (leftKanDiagram δ F c) := ⟨z.val, z.property.trans hbase⟩
    refine ⟨z', (kanIsRelativeColimitCone_congr sj.π hbase z z' rfl).1 hz, ?_⟩
    apply sj.hom_ext
    · rw [Category.assoc, sj.π_fst]
      change z.val ≫ (pre (boundary (n + 1)).ι).app D =
        (leftKanCanonicalCocone δ H₀ c).val ≫ sj.fst
      rw [hzA]
      change SerrePositivity.InfinityCategories.F1B.functorTranspose a = j ≫ H₀ ≫ sj.fst
      rw [h₀A]
      exact SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose _
    · rw [Category.assoc, sj.π_snd]
      change z.val ≫ (ihom (Δ[n + 1] : SSet.{u})).map U =
        (leftKanCanonicalCocone δ H₀ c).val ≫ sj.snd
      rw [hzG]
      change SerrePositivity.InfinityCategories.F1B.functorTranspose g = j ≫ H₀ ≫ sj.snd
      rw [h₀G]
      exact SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose _
  obtain ⟨H, hHF, hH₀, _⟩ :=
    exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits
      sj.π hsj δ hδ F H₀ hFH₀ hlocal
  refine ⟨H, hHF, ?_, ?_⟩
  · have h := congrArg (fun f ↦ f ≫ sj.fst) hH₀
    rw [Category.assoc, sj.π_fst, h₀A] at h
    exact h
  · have h := congrArg (fun f ↦ f ≫ sj.snd) hH₀
    rw [Category.assoc, sj.π_snd, h₀G] at h
    exact h

end SerrePositivity.InfinityCategories.F1B
