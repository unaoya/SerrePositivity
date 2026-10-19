module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeHomDiagramExtension
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinInvertingRestriction

/-!
概要：cocartesian fibration 間の単射が誘導する相対指数の制限は inner fibration。
方針：底の射を curry の全単射で固定し、内ホーンと部分図式を同時に保つ延長を使う。
規約：共通の底の quasicategory 性は不要。
使われ方：相対 join の制限射自体の充填性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：底上の単射による図式の族の制限は inner fibration。
方針：可換正方形を実際の逆像上の整合する図式に戻し、両方を固定して延長する。
規約：両側の元の射影は cocartesian fibration、標的だけ quasicategory。
使われ方：fiber の cartesian 性から制限の全空間の cartesian 性へ移す前提。 -/
instance kanFiberwiseHomPre_innerFibration {C D : SSet.{u}} [Quasicategory D]
    {K L : Over C} (i : K ⟶ L) [Mono i.left]
    [CocartesianFibration K.hom] [CocartesianFibration L.hom] :
    InnerFibration (kanFiberwiseHomPre (D := D) i) where
  mem := by
    intro A B j hj
    constructor
    intro a b sq
    let c := b ≫ kanFiberwiseHomProjection K.hom D
    have ha : a ≫ kanFiberwiseHomProjection L.hom D = j ≫ c := by
      rw [← kanFiberwiseHomPre_projection i, ← Category.assoc, sq.w, Category.assoc]
    let F := (kanFiberwiseHomEquiv (D := D) K.hom c).symm ⟨b, rfl⟩
    let G := (kanFiberwiseHomEquiv (D := D) L.hom (j ≫ c)).symm ⟨a, ha⟩
    have hF : kanFiberwiseHomCurry K.hom c F = b :=
      congrArg Subtype.val ((kanFiberwiseHomEquiv (D := D) K.hom c).apply_symm_apply ⟨b, rfl⟩)
    have hG : kanFiberwiseHomCurry L.hom (j ≫ c) G = a :=
      congrArg Subtype.val ((kanFiberwiseHomEquiv (D := D) L.hom (j ≫ c)).apply_symm_apply ⟨a, ha⟩)
    let u : Over.mk (j ≫ c) ⟶ Over.mk c := Over.homMk j rfl
    have hFG : (overPullbackUnderlying K.hom).map u ≫ F =
        overPullbackMap i (Over.mk (j ≫ c)) ≫ G := by
      apply kanFiberwiseHomCurry_injective K.hom (j ≫ c)
      erw [kanFiberwiseHomCurry_precomp, kanFiberwiseHomCurry_pre i, hF, hG]
      exact sq.w.symm
    obtain ⟨H, hHK, hHL⟩ := exists_kanRelativeHomDiagram_extension i u hj F G hFG
    refine CommSq.HasLift.mk' {
      l := kanFiberwiseHomCurry L.hom c H
      fac_left := ?_
      fac_right := ?_ }
    · rw [← kanFiberwiseHomCurry_precomp]
      change kanFiberwiseHomCurry L.hom (j ≫ c) ((overPullbackUnderlying L.hom).map u ≫ H) = _
      rw [hHL, hG]
    · erw [← kanFiberwiseHomCurry_pre i, hHK]
      exact hF

/-- 概要：相対 join の左包含は単射。
方針：通常の join への射影に合成すると単射な左包含になる。
規約：元の二つの構造射は任意。
使われ方：相対指数の制限の一般の inner fibration 判定への適用。 -/
instance kanRelativeJoinInl_mono {K L C : SSet.{u}} (p : K ⟶ C) (q : L ⟶ C) :
    Mono (relativeJoinInl p q) := mono_of_mono_fac (relativeJoinInl_fst p q)

/-- 概要：相対 join の図式の族を元の図式へ制限する射自体が inner fibration。
方針：左包含の単射性と両側の底への cocartesian fibration 性を一般の判定に渡す。
規約：底の quasicategory 性は要求しない。
使われ方：V の fiber の cartesian 性を全空間へ移すための前提。 -/
lemma kanRelativeJoinRestriction_innerFibration {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) [CocartesianFibration p] :
    InnerFibration (kanFiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)) := by
  have : Mono (kanRelativeJoinInlOver p).left :=
    inferInstanceAs (Mono (relativeJoinInl p (𝟙 C)))
  have : CocartesianFibration (Over.mk p).hom := inferInstanceAs (CocartesianFibration p)
  have : CocartesianFibration (Over.mk (relativeJoinBaseProjection p (𝟙 C))).hom :=
    inferInstanceAs (CocartesianFibration (relativeJoinBaseProjection p (𝟙 C)))
  exact kanFiberwiseHomPre_innerFibration (kanRelativeJoinInlOver p)

end SerrePositivity.InfinityCategories.F1B
