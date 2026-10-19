module

public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomFiberPostcomposition
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseRelativeRestriction
public import SerrePositivity.InfinityCategories.F1B.KanPullbackOverFiber
public import SerrePositivity.InfinityCategories.F1B.KanRelativeCoconeRestriction

/-!
概要：全空間の相対余錐比較の標的の fiber を通常の相対余錐の標的と同定する。
方針：引き戻しと fiber の交換を使い、前後合成を保つ関手空間の同型を合わせる。
規約：構造射と標的の射は任意。
使われ方：変動する添字の相対普遍性を各 fiber で判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対余錐制限の標的は全空間の相対比較の標的の fiber と同型。
方針：各関手空間の標準同型で引き戻しを移し、底の fiber との交換同型を合成する。
規約：第一成分は元の図式、第二成分は標的での全余錐。
使われ方：全空間の相対比較を通常の相対余錐制限と照合する。 -/
def kanRelativeJoinRelativeTargetFiberIso {K C D E : SSet.{u}}
    (p : K ⟶ C) (c : C _⦋0⦌) (U : D ⟶ E) :
    KanRelativeCoconeTarget (vertexFiber p c) U ≅
      vertexFiber (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) U) c :=
  asIso (pullback.map _ _ _ _
    (kanFiberwiseHomFiberIso p c D).hom
    (kanRelativeJoinCoconeFiberIso p c E).hom
    (kanFiberwiseHomFiberIso p c E).hom
    (kanFiberwiseHomFiberIso_postcomp p c U).symm
    (kanRelativeJoinCoconeFiberIso_restriction p c).symm) ≪≫
  (kanPullbackOverFiberIso
    (kanFiberwiseHomProjection p D)
    (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) E)
    (kanFiberwiseHomProjection p E)
    (kanFiberwiseHomPostcomp p U)
    (kanFiberwiseHomPre (D := E) (kanRelativeJoinInlOver p))
    (kanFiberwiseHomPostcomp_projection p U)
    (kanFiberwiseHomPre_projection (kanRelativeJoinInlOver p)) c).symm

/-- 概要：相対標的の fiber の同型は元の図式の成分を保つ。
方針：引き戻しの交換同型と引き戻し間の射の第一射影を計算する。
規約：fiber の包含後の全空間の射として記す。
使われ方：相対比較の第一成分の同定。 -/
@[reassoc]
lemma kanRelativeJoinRelativeTargetFiberIso_fst {K C D E : SSet.{u}}
    (p : K ⟶ C) (c : C _⦋0⦌) (U : D ⟶ E) :
    (kanRelativeJoinRelativeTargetFiberIso p c U).hom ≫
        vertexFiberι (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) U) c ≫
        pullback.fst (kanFiberwiseHomPostcomp p U)
          (kanFiberwiseHomPre (D := E) (kanRelativeJoinInlOver p)) =
      pullback.fst ((ihom (vertexFiber p c)).map U) (coconeRestriction (vertexFiber p c) E) ≫
        (kanFiberwiseHomFiberIso p c D).hom ≫ vertexFiberι (kanFiberwiseHomProjection p D) c := by
  simp only [kanRelativeJoinRelativeTargetFiberIso, Iso.trans_hom, asIso_hom,
    Iso.symm_hom, Category.assoc]
  erw [kanPullbackOverFiberIso_inv_fst]
  simp only [pullback.map]
  erw [pullback.lift_fst_assoc]
  exact Category.assoc _ _ _

/-- 概要：相対標的の fiber の同型は標的の全余錐の成分を保つ。
方針：引き戻しの交換同型と引き戻し間の射の第二射影を計算する。
規約：底での余錐全体の射を保持する。
使われ方：相対比較の第二成分の同定。 -/
@[reassoc]
lemma kanRelativeJoinRelativeTargetFiberIso_snd {K C D E : SSet.{u}}
    (p : K ⟶ C) (c : C _⦋0⦌) (U : D ⟶ E) :
    (kanRelativeJoinRelativeTargetFiberIso p c U).hom ≫
        vertexFiberι (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) U) c ≫
        pullback.snd (kanFiberwiseHomPostcomp p U)
          (kanFiberwiseHomPre (D := E) (kanRelativeJoinInlOver p)) =
      pullback.snd ((ihom (vertexFiber p c)).map U) (coconeRestriction (vertexFiber p c) E) ≫
        (kanRelativeJoinCoconeFiberIso p c E).hom ≫
        vertexFiberι (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) E) c := by
  simp only [kanRelativeJoinRelativeTargetFiberIso, Iso.trans_hom, asIso_hom,
    Iso.symm_hom, Category.assoc]
  erw [kanPullbackOverFiberIso_inv_snd]
  simp only [pullback.map]
  erw [pullback.lift_snd_assoc]
  exact Category.assoc _ _ _

/-- 概要：全空間の相対比較は各 fiber で通常の相対余錐制限と一致する。
方針：引き戻しの二射影へ合成し、余錐の制限と後合成の自然性を照合する。
規約：等式は標的の fiber を全空間へ含めた形。
使われ方：局所の相対余錐条件を変動する添字の全空間へ移す。 -/
lemma kanRelativeJoinRelativeFiber_comparison {K C D E : SSet.{u}}
    (p : K ⟶ C) (c : C _⦋0⦌) (U : D ⟶ E) :
    (kanRelativeJoinCoconeFiberIso p c D).hom ≫
        vertexFiberι (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D) c ≫
        kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U =
      kanRelativeCoconeRestriction (vertexFiber p c) U ≫
        (kanRelativeJoinRelativeTargetFiberIso p c U).hom ≫
        vertexFiberι (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) U) c := by
  apply pullback.hom_ext
  · simp only [Category.assoc, kanFiberwiseRelativeRestriction_fst]
    erw [kanRelativeJoinRelativeTargetFiberIso_fst]
    erw [reassoc_of% (kanRelativeCoconeRestriction_fst (vertexFiber p c) U)]
    have h := congrArg (fun z ↦ z ≫ vertexFiberι (kanFiberwiseHomProjection p D) c)
      (kanRelativeJoinCoconeFiberIso_restriction (D := D) p c)
    simp only [Category.assoc, kanFiberwiseHomPreFiber] at h
    exact h
  · simp only [Category.assoc, kanFiberwiseRelativeRestriction_snd]
    erw [kanRelativeJoinRelativeTargetFiberIso_snd]
    erw [reassoc_of% (kanRelativeCoconeRestriction_snd (vertexFiber p c) U)]
    have h := congrArg (fun z ↦ z ≫
      vertexFiberι (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) E) c)
      (kanRelativeJoinCoconeFiberIso_postcomp p c U)
    simp only [Category.assoc, kanFiberwiseHomPostcompFiber, vertexFiberMap_ι] at h
    exact h

/-- 概要：各 fiber の相対比較は相対余錐制限を標準同型で移した射。
方針：fiber の包含の単射性で全空間への比較の等式に帰着する。
規約：始域と標的の同型の向きは通常の余錐から全空間の fiber へ。
使われ方：fiber ごとの相対普遍性の移送。 -/
lemma kanRelativeJoinRelativeFiber_restriction {K C D E : SSet.{u}}
    (p : K ⟶ C) (c : C _⦋0⦌) (U : D ⟶ E) :
    (kanRelativeJoinCoconeFiberIso p c D).hom ≫
        kanFiberwiseRelativeRestrictionFiber (kanRelativeJoinInlOver p) U c =
      kanRelativeCoconeRestriction (vertexFiber p c) U ≫
        (kanRelativeJoinRelativeTargetFiberIso p c U).hom := by
  apply vertexFiber_hom_ext (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) U) c
  simp only [Category.assoc, kanFiberwiseRelativeRestrictionFiber, vertexFiberMap_ι]
  exact kanRelativeJoinRelativeFiber_comparison p c U

/-- 概要：局所余錐の相対始点境界充填は全空間の相対比較の fiber に移る。
方針：相対余錐制限と fiber の相対比較を結ぶ二つの同型で充填性を移送する。
規約：全空間での充填性はまだ主張せず、一つの fiber の射を扱う。
使われ方：変動する添字の相対的な組み立ての局所入力。 -/
lemma kanRelativeJoinRelativeFiber_initialBoundary {K C D E : SSet.{u}}
    (p : K ⟶ C) (c : C _⦋0⦌) (U : D ⟶ E)
    {d : vertexFiber p c ⟶ D} {z : JoinCocone d} (hz : KanRelativeCoconeLifting U z) :
    InitialBoundaryLifting
      (kanFiberwiseRelativeRestrictionFiber (kanRelativeJoinInlOver p) U c)
      ((kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
        (functorVertex z.val)) :=
  hz.map_iso (kanRelativeJoinCoconeFiberIso p c D)
    (kanRelativeJoinRelativeTargetFiberIso p c U) (kanRelativeJoinRelativeFiber_restriction p c U)

end SerrePositivity.InfinityCategories.F1B
