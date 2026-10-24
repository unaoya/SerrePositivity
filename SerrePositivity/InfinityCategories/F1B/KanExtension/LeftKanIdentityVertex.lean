module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceIdentityTerminal
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulBaseChange
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal

/-!
概要：包含の像の点で左 Kan の局所添字に恒等射の終対象を構成する。
方針：恒等射を slice への引き戻しへ持ち上げ、充満忠実な引き戻し射影で終対象性を反映する。
規約：包含には inner 性と写像空間の充満忠実性を明示する。
使われ方：全部分圏包含に沿う Kan 拡張の単位の可逆性と厳密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：像の点の局所添字に元の頂点の恒等射を含める。
方針：元の頂点と slice の恒等頂点の対を引き戻しへ持ち上げる。
規約：fibration 性や充満忠実性は構成には不要。
使われ方：全部分圏の像の点における局所 Kan 条件の評価。 -/
def kanLeftKanIdentityVertex {K C : SSet.{u}} (δ : K ⟶ C) (k : K _⦋0⦌) :
    (leftKanShape δ (δ.app (Opposite.op ⦋0⦌) k)) _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm k)
    (SSet.yonedaEquiv.symm (sliceIdentityCone (δ.app (Opposite.op ⦋0⦌) k))) (by
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp,
        sliceIdentityCone_projection]))

/-- 概要：局所添字の恒等頂点の元の添字への射影は元の頂点。
方針：引き戻しの第一射影を Yoneda 同値で評価する。
規約：零単体の厳密な等式。
使われ方：Kan の単位の成分を局所余錐の恒等頂点の脚と同定する。 -/
lemma kanLeftKanIdentityVertex_projection {K C : SSet.{u}} (δ : K ⟶ C) (k : K _⦋0⦌) :
    (leftKanProjection δ (δ.app (Opposite.op ⦋0⦌) k)).app (Opposite.op ⦋0⦌)
      (kanLeftKanIdentityVertex δ k) = k := by
  rw [kanLeftKanIdentityVertex, ← SSet.yonedaEquiv_comp, pullback.lift_fst]
  exact SSet.yonedaEquiv.apply_symm_apply k

/-- 概要：局所添字の恒等頂点を slice へ写すと恒等射になる。
方針：引き戻しの第二射影を Yoneda 同値で評価する。
規約：sliceIdentityCone 自身との等式。
使われ方：局所添字へ終対象性を反映する。 -/
lemma kanLeftKanIdentityVertex_slice {K C : SSet.{u}} (δ : K ⟶ C) (k : K _⦋0⦌) :
    (pullback.snd δ
      (sliceOverProjection (SSet.yonedaEquiv.symm (δ.app (Opposite.op ⦋0⦌) k)))).app
        (Opposite.op ⦋0⦌) (kanLeftKanIdentityVertex δ k) =
      sliceIdentityCone (δ.app (Opposite.op ⦋0⦌) k) := by
  rw [kanLeftKanIdentityVertex, ← SSet.yonedaEquiv_comp, pullback.lift_snd]
  exact SSet.yonedaEquiv.apply_symm_apply _

/-- 概要：充満忠実な inner 包含の像の点では局所添字の恒等射が終対象。
方針：引き戻しの第二射影の充満忠実性で slice の恒等射の終対象性を反映する。
規約：充満忠実性は h 圏の条件に弱めない。
使われ方：元の図式への制限を保つ Kan 拡張の厳密な存在。 -/
lemma kanLeftKanIdentityVertex_isTerminal {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (δ : K ⟶ C) [InnerFibration δ]
    (hδ : IsFullyFaithful δ) (k : K _⦋0⦌) :
    IsTerminalVertex (kanLeftKanIdentityVertex δ k) := by
  let q := sliceOverProjection (SSet.yonedaEquiv.symm (δ.app (Opposite.op ⦋0⦌) k))
  have : InnerFibration (pullback.snd δ q) :=
    ⟨innerFibrations.pullback_snd δ q (InnerFibration.mem (q := δ))⟩
  have : Quasicategory (leftKanShape δ (δ.app (Opposite.op ⦋0⦌) k)) :=
    quasicategory_of_innerFibration (pullback.snd δ q)
  apply (hδ.pullback_snd q).reflects_isTerminalVertex
  rw [kanLeftKanIdentityVertex_slice]
  exact SerrePositivity.InfinityCategories.F1B.sliceIdentityCone_isTerminalVertex _

end SerrePositivity.InfinityCategories.F1B
