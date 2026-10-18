module

public import SerrePositivity.KST.Comparison.DiagramArrowFibers
public import SerrePositivity.KST.Comparison.CommonTrivialRefinement
public import SerrePositivity.KST.Comparison.TrivialFibrationExtension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-!
# 単射な基底の span の厳密化

概要：単射な二つの基底射と Kan な中央の基底の下で、homotopy-cartesian な span を厳密化する。
方針：二つのファイバーの共通の trivial fibration の模型を、単射に沿って端点へ延長する。
規約：Segal 1974 Lemma 1.7。Mather 1976 の WCHP の経路とは異なるスライスの延長による証明。
使われ方：成分ごとの局所化同型の中間 span を通して、証明済みの厳密な場合へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：単射な基底射を持ち中央の基底が Kan の場合、homotopy-cartesian な span の射を厳密な模型へ置換できる。
方針：共通の trivial fibration の模型を端点へ延長し、元の span と厳密な span を結ぶ中間 span を作る。
規約：縦射は Kan fibration とする。全ての比較と因子化を実際の自然変換として構成する。
使われ方：Segal Lemma 1.7 の単射な基底の場合。
-/
theorem spanStrictification_of_mono {F G : WalkingSpan ⥤ SSet.{u}}
    [SSet.KanComplex (G.obj .zero)] [Mono (G.map WalkingSpan.Hom.fst)]
    [Mono (G.map WalkingSpan.Hom.snd)] (α : F ⟶ G)
    (hα : ∀ d, SSet.modelCategoryQuillen.J.rlp (α.app d))
    (hL : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.fst) α))
    (hR : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.snd) α)) :
    ∃ (H K : WalkingSpan ⥤ SSet.{u}) (u : H ⟶ F) (v : H ⟶ K) (β : K ⟶ G),
      u ≫ α = v ≫ β ∧
      (∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (u.app d))) ∧
      (∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (v.app d))) ∧
      (∀ d, SSet.modelCategoryQuillen.J.rlp (β.app d)) ∧
      IsPullback (K.map WalkingSpan.Hom.fst) (β.app .zero) (β.app .left)
        (G.map WalkingSpan.Hom.fst) ∧
      IsPullback (K.map WalkingSpan.Hom.snd) (β.app .zero) (β.app .right)
        (G.map WalkingSpan.Hom.snd) := by
  let EL := diagramArrowFiber α WalkingSpan.Hom.fst
  let ER := diagramArrowFiber α WalkingSpan.Hom.snd
  let pL : EL ⟶ G.obj .zero := pullback.fst (G.map WalkingSpan.Hom.fst) (α.app .left)
  let pR : ER ⟶ G.obj .zero := pullback.fst (G.map WalkingSpan.Hom.snd) (α.app .right)
  let jL : EL ⟶ F.obj .left := pullback.snd (G.map WalkingSpan.Hom.fst) (α.app .left)
  let jR : ER ⟶ F.obj .right := pullback.snd (G.map WalkingSpan.Hom.snd) (α.app .right)
  let tL := diagramArrowFiberComparison α WalkingSpan.Hom.fst
  let tR := diagramArrowFiberComparison α WalkingSpan.Hom.snd
  have htLp : tL ≫ pL = α.app .zero := pullback.lift_fst ..
  have htRp : tR ≫ pR = α.app .zero := pullback.lift_fst ..
  have htLj : tL ≫ jL = F.map WalkingSpan.Hom.fst := pullback.lift_snd ..
  have htRj : tR ≫ jR = F.map WalkingSpan.Hom.snd := pullback.lift_snd ..
  have hpL : SSet.modelCategoryQuillen.J.rlp pL :=
    SSet.modelCategoryQuillen.J.rlp.pullback_fst _ _ (hα .left)
  have hpR : SSet.modelCategoryQuillen.J.rlp pR :=
    SSet.modelCategoryQuillen.J.rlp.pullback_fst _ _ (hα .right)
  let : SSet.KanComplex EL := diagramArrowFiber_kanComplex α WalkingSpan.Hom.fst (hα .left)
  let : SSet.KanComplex ER := diagramArrowFiber_kanComplex α WalkingSpan.Hom.snd (hα .right)
  have htL : IsIso (AnodyneHomotopy.anodyneQ.map tL) :=
    (diagramArrowFiberComparison_isIso_iff α WalkingSpan.Hom.fst (hα .left)).mpr hL
  have htR : IsIso (AnodyneHomotopy.anodyneQ.map tR) :=
    (diagramArrowFiberComparison_isIso_iff α WalkingSpan.Hom.snd (hα .right)).mpr hR
  obtain ⟨Z, i, rL, rR, hi, hirL, hirR, hbase, hrL, hrR⟩ :=
    commonTrivialFibrationRefinement pL pR hpL hpR tL tR (htLp.trans htRp.symm) htL htR
  let : Mono jL := inferInstanceAs (Mono (pullback.snd (G.map WalkingSpan.Hom.fst) (α.app .left)))
  let : Mono jR := inferInstanceAs (Mono (pullback.snd (G.map WalkingSpan.Hom.snd) (α.app .right)))
  obtain ⟨A₀, eL, iL, heL, hiL⟩ := trivialFibrationExtension jL rL hrL
  obtain ⟨B₀, eR, iR, heR, hiR⟩ := trivialFibrationExtension jR rR hrR
  let c := rL ≫ pL
  have hsqL : IsPullback iL c (eL ≫ α.app .left) (G.map WalkingSpan.Hom.fst) :=
    hiL.paste_vert (IsPullback.of_hasPullback (G.map WalkingSpan.Hom.fst) (α.app .left)).flip
  have hsqR : IsPullback iR c (eR ≫ α.app .right) (G.map WalkingSpan.Hom.snd) := by
    have h : IsPullback iR (rR ≫ pR) (eR ≫ α.app .right) (G.map WalkingSpan.Hom.snd) :=
      hiR.paste_vert
      (IsPullback.of_hasPullback (G.map WalkingSpan.Hom.snd) (α.app .right)).flip
    rw [← hbase] at h
    exact h
  let K := span iL iR
  let β : K ⟶ G := spanHomMk c (eL ≫ α.app .left) (eR ≫ α.app .right) hsqL.w hsqR.w
  let H := span (i ≫ iL) (i ≫ iR)
  let u : H ⟶ F := spanHomMk (𝟙 _) eL eR (by
    change (i ≫ iL) ≫ eL = (𝟙 _) ≫ F.map WalkingSpan.Hom.fst
    rw [Category.assoc, hiL.w, ← Category.assoc, hirL, htLj, Category.id_comp]) (by
    change (i ≫ iR) ≫ eR = (𝟙 _) ≫ F.map WalkingSpan.Hom.snd
    rw [Category.assoc, hiR.w, ← Category.assoc, hirR, htRj, Category.id_comp])
  let v : H ⟶ K := spanHomMk i (𝟙 _) (𝟙 _) (by simp [H, K]) (by simp [H, K])
  have hiQ : IsIso (AnodyneHomotopy.anodyneQ.map i) :=
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _ hi
  have heLQ : IsIso (AnodyneHomotopy.anodyneQ.map eL) :=
    MonoRightLiftingContraction.localized_isIso _ heL
  have heRQ : IsIso (AnodyneHomotopy.anodyneQ.map eR) :=
    MonoRightLiftingContraction.localized_isIso _ heR
  have hrLK : SSet.modelCategoryQuillen.J.rlp rL :=
    fun _ _ f hf => hrL f (SSet.modelCategoryQuillen.J_le_monomorphisms _ hf)
  have heLK : SSet.modelCategoryQuillen.J.rlp eL :=
    fun _ _ f hf => heL f (SSet.modelCategoryQuillen.J_le_monomorphisms _ hf)
  have heRK : SSet.modelCategoryQuillen.J.rlp eR :=
    fun _ _ f hf => heR f (SSet.modelCategoryQuillen.J_le_monomorphisms _ hf)
  refine ⟨H, K, u, v, β, ?_, ?_, ?_, ?_, hsqL, hsqR⟩
  · apply NatTrans.ext
    funext d
    rcases d with (_ | _ | _)
    · change (𝟙 _) ≫ α.app .zero = i ≫ (rL ≫ pL)
      rw [Category.id_comp, ← Category.assoc, hirL, htLp]
    · change eL ≫ α.app .left = (𝟙 _) ≫ (eL ≫ α.app .left)
      simp
    · change eR ≫ α.app .right = (𝟙 _) ≫ (eR ≫ α.app .right)
      simp
  · intro d
    rcases d with (_ | _ | _)
    · change IsIso (AnodyneHomotopy.anodyneQ.map (𝟙 _)); infer_instance
    · exact heLQ
    · exact heRQ
  · intro d
    rcases d with (_ | _ | _)
    · exact hiQ
    · change IsIso (AnodyneHomotopy.anodyneQ.map (𝟙 _)); infer_instance
    · change IsIso (AnodyneHomotopy.anodyneQ.map (𝟙 _)); infer_instance
  · intro d
    rcases d with (_ | _ | _)
    · exact SSet.modelCategoryQuillen.J.rlp.comp_mem _ _ hrLK hpL
    · exact SSet.modelCategoryQuillen.J.rlp.comp_mem _ _ heLK (hα .left)
    · exact SSet.modelCategoryQuillen.J.rlp.comp_mem _ _ heRK (hα .right)

end SerrePositivity.KST.Comparison
