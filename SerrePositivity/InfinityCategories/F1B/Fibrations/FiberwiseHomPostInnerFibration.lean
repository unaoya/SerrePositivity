module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.FiberwiseHomPostcomposition
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinInvertingRestriction
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianInnerAnodynePullback
public import SerrePositivity.InfinityCategories.Core.PrecompositionRelativeLifting

/-!
概要：標的への後合成が誘導する全空間の射の inner fibration 性。
方針：内ホーンの逆像の単射な前合成同値に対する持ち上げを curry する。
規約：標的の射の持ち上げ条件を明示する。
使われ方：全空間の相対比較の標的の充填性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：単射な前合成同値に対する持ち上げを持つ射の全空間の後合成は inner fibration。
方針：底の射を固定して正方形を逆像上へ移し、内ホーンの逆像に対して充填する。
規約：元の射影は cocartesian fibration、底に充填性は不要。
使われ方：相対比較の標的の引き戻しを inner fibration として扱う。 -/
lemma fiberwiseHomPostcomp_innerFibration {K C D E : SSet.{u}}
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E)
    (hU : ∀ {X Y : SSet.{u}} (m : X ⟶ Y), Mono m →
      IsPrecompositionEquivalence m → HasLiftingProperty m U) :
    InnerFibration (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p U) where
  mem := by
    intro A B j hj
    constructor
    intro a b sq
    let c := b ≫ SerrePositivity.InfinityCategories.fiberwiseHomProjection p E
    have ha : a ≫ SerrePositivity.InfinityCategories.fiberwiseHomProjection p D = j ≫ c := by
      rw [← SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp_projection p U, ← Category.assoc, sq.w, Category.assoc]
    let F := (SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := E) p c).symm ⟨b, rfl⟩
    let G := (SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) p (j ≫ c)).symm ⟨a, ha⟩
    have hF : SerrePositivity.InfinityCategories.fiberwiseHomCurry p c F = b :=
      congrArg Subtype.val ((SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := E) p c).apply_symm_apply ⟨b, rfl⟩)
    have hG : SerrePositivity.InfinityCategories.fiberwiseHomCurry p (j ≫ c) G = a :=
      congrArg Subtype.val ((SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) p (j ≫ c)).apply_symm_apply ⟨a, ha⟩)
    let u : Over.mk (j ≫ c) ⟶ Over.mk c := Over.homMk j rfl
    have : Mono j := by cases hj; infer_instance
    have hm : Mono ((overPullbackUnderlying p).map u) :=
      (overPullbackProjection_isPullback p u).mono_fst_of_mono
    have : HasLiftingProperty ((overPullbackUnderlying p).map u) U := hU _ hm
      (SerrePositivity.InfinityCategories.cocartesianFibration_overPullback_innerHorn_isPrecompositionEquivalence p u hj)
    have sq' : CommSq G ((overPullbackUnderlying p).map u) U F := by
      constructor
      apply SerrePositivity.InfinityCategories.fiberwiseHomCurry_injective p (j ≫ c)
      calc
        SerrePositivity.InfinityCategories.fiberwiseHomCurry p (j ≫ c) (G ≫ U) =
            SerrePositivity.InfinityCategories.fiberwiseHomCurry p (j ≫ c) G ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p U :=
          SerrePositivity.InfinityCategories.F1B.fiberwiseHomCurry_postcomp p U (j ≫ c) G
        _ = a ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p U := congrArg (· ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p U) hG
        _ = j ≫ b := sq.w
        _ = j ≫ SerrePositivity.InfinityCategories.fiberwiseHomCurry p c F := congrArg (j ≫ ·) hF.symm
        _ = _ := (SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp p j c F).symm
    refine CommSq.HasLift.mk' {
      l := SerrePositivity.InfinityCategories.fiberwiseHomCurry p c sq'.lift
      fac_left := ?_
      fac_right := ?_ }
    · rw [← SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp]
      change SerrePositivity.InfinityCategories.fiberwiseHomCurry p (j ≫ c) ((overPullbackUnderlying p).map u ≫ sq'.lift) = a
      rw [sq'.fac_left, hG]
    · rw [← SerrePositivity.InfinityCategories.F1B.fiberwiseHomCurry_postcomp, sq'.fac_right, hF]

/-- 概要：単射による関手の制限の全空間の後合成は inner fibration。
方針：関手の制限の持ち上げ性を一般の後合成の判定へ渡す。
規約：値域 X は quasicategory。
使われ方：境界を固定する関手圏を標的とする相対 Kan の組み立て。 -/
instance fiberwiseHomPostcomp_pre_innerFibration {K C P Q X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ C) [CocartesianFibration p] (v : P ⟶ Q) [Mono v] :
    InnerFibration (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p ((pre v).app X)) := by
  apply fiberwiseHomPostcomp_innerFibration
  intro Y Z m hm he
  have : Mono m := hm
  exact he.hasLiftingProperty_pre v X

end SerrePositivity.InfinityCategories.F1B
