module

public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomPostcomposition
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinCoconeFiber

/-!
概要：fiber ごとの関手圏の同定は標的への後合成を保つ。
方針：全パラメータの Hom 比較の定値逆像表示と、curry の後合成の自然性を使う。
規約：全ての対象と射は任意。
使われ方：全空間の相対比較の fiber を通常の相対余錐制限と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：fiber の全パラメータ Hom 比較は標的への後合成と可換。
方針：fiber の包含へ合成し、定値逆像上の図式の後合成を照合する。
規約：パラメータ T は任意。
使われ方：fiber の比較同型の自然性。 -/
lemma kanFiberwiseHomFiberHomEquiv_postcomp {K C D E T : SSet.{u}}
    (p : K ⟶ C) (c : C _⦋0⦌) (U : D ⟶ E)
    (h : T ⟶ (ihom (vertexFiber p c)).obj D) :
    kanFiberwiseHomFiberHomEquiv p c E T (h ≫ (ihom (vertexFiber p c)).map U) =
      kanFiberwiseHomFiberHomEquiv p c D T h ≫ kanFiberwiseHomPostcompFiber p U c := by
  apply vertexFiber_hom_ext (kanFiberwiseHomProjection p E) c
  rw [Category.assoc]
  change _ = kanFiberwiseHomFiberHomEquiv p c D T h ≫
    vertexFiberMap _ _ (kanFiberwiseHomPostcomp p U) (kanFiberwiseHomPostcomp_projection p U) c ≫ _
  rw [vertexFiberMap_ι, ← Category.assoc, kanFiberwiseHomFiberHomEquiv_apply_ι,
    kanFiberwiseHomFiberHomEquiv_apply_ι, ← kanFiberwiseHomCurry_postcomp]
  congr 1

/-- 概要：fiber と通常の関手圏の同型は標的の関手の後合成を同定する。
方針：全パラメータ Hom 比較の自然性を恒等射へ適用する。
規約：底の頂点 c を固定する。
使われ方：相対比較の fiber の二つの成分の同定。 -/
lemma kanFiberwiseHomFiberIso_postcomp {K C D E : SSet.{u}}
    (p : K ⟶ C) (c : C _⦋0⦌) (U : D ⟶ E) :
    (kanFiberwiseHomFiberIso p c D).hom ≫ kanFiberwiseHomPostcompFiber p U c =
      (ihom (vertexFiber p c)).map U ≫ (kanFiberwiseHomFiberIso p c E).hom := by
  change kanFiberwiseHomFiberHomEquiv p c D _ (𝟙 _) ≫
    kanFiberwiseHomPostcompFiber p U c = _
  rw [← kanFiberwiseHomFiberHomEquiv_postcomp, Category.id_comp,
    kanFiberwiseHomFiberIso_hom_comp]

/-- 概要：相対 join の fiber の余錐の関手空間の同型も後合成を保つ。
方針：fiber の Hom 同型の後合成の自然性と、始域の同型による前合成の自然性を合わせる。
規約：相対 join の元の構造射は任意。
使われ方：全空間の相対余錐比較の fiber の厳密な表示。 -/
lemma kanRelativeJoinCoconeFiberIso_postcomp {K C D E : SSet.{u}}
    (p : K ⟶ C) (c : C _⦋0⦌) (U : D ⟶ E) :
    (kanRelativeJoinCoconeFiberIso p c D).hom ≫
        kanFiberwiseHomPostcompFiber (relativeJoinBaseProjection p (𝟙 C)) U c =
      (ihom (join (vertexFiber p c) (Δ[0] : SSet.{u}))).map U ≫
        (kanRelativeJoinCoconeFiberIso p c E).hom := by
  dsimp only [kanRelativeJoinCoconeFiberIso, Iso.trans_hom]
  rw [Category.assoc, kanFiberwiseHomFiberIso_postcomp]
  have h := (pre (kanRelativeJoinBaseFiberIso p c).inv).naturality U
  exact (congrArg (fun z ↦ z ≫
    (kanFiberwiseHomFiberIso (relativeJoinBaseProjection p (𝟙 C)) c E).hom) h).symm

end SerrePositivity.InfinityCategories.F1B
