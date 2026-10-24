module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftKanIdentityVertex
public import SerrePositivity.InfinityCategories.F1B.Cofinality.TerminalPointAnodyne
public import SerrePositivity.InfinityCategories.Stable.IdentityCocone
public import SerrePositivity.InfinityCategories.Stable.ColimitRestriction
public import SerrePositivity.InfinityCategories.Stable.CoconeLeg
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：包含の像の点で標準左 Kan 余錐を恒等射へ制限すると定値になる。
方針：局所添字の第二射影と slice の展開の自然性を計算する。
規約：包含に充満忠実性や fibration 性を要求しない。
使われ方：輸送された余錐の脚と指定 Kan 単位の成分の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：標準左 Kan 余錐を像の点の恒等射で制限すると定値余錐になる。
方針：slice への引き戻しの第二射影の値が恒等錐であることを展開する。
規約：元の標準余錐の射の厳密な等式。
使われ方：指定 Kan 変換の局所輸送の終端の脚を同定する。 -/
lemma kanLeftCanonical_identity_restrict_val {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (k : K _⦋0⦌) :
    joinMap (SSet.yonedaEquiv.symm (kanLeftKanIdentityVertex δ k)) (𝟙 (Δ[0] : SSet.{u})) ≫
        (leftKanCanonicalCocone δ F (δ.app (Opposite.op ⦋0⦌) k)).val =
      SSet.const (F.app (Opposite.op ⦋0⦌) (δ.app (Opposite.op ⦋0⦌) k)) := by
  change joinMap _ _ ≫ (sliceOverUncurry _ ≫ F) = _
  rw [← Category.assoc, ← sliceOverUncurry_precomp]
  have hp : SSet.yonedaEquiv.symm (kanLeftKanIdentityVertex δ k) ≫
      pullback.snd δ
        (sliceOverProjection (SSet.yonedaEquiv.symm (δ.app (Opposite.op ⦋0⦌) k))) =
      SSet.yonedaEquiv.symm (sliceIdentityCone (δ.app (Opposite.op ⦋0⦌) k)) := by
    rw [SSet.yonedaEquiv_symm_comp, kanLeftKanIdentityVertex_slice]
  rw [hp, sliceOverUncurry_yoneda]
  change SSet.const (δ.app (Opposite.op ⦋0⦌) k) ≫ F = _
  exact SSet.const_comp _ F

/-- 概要：標準左 Kan 余錐の恒等射での脚は可逆。
方針：定値余錐の脚の一次単体を恒等辺と同定する。
規約：標的の quasicategory 性は不要。
使われ方：局所輸送の自然性で指定単位の可逆性を回収する。 -/
lemma kanLeftCanonical_identity_leg_invertible {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (k : K _⦋0⦌) :
    IsInvertibleEdge ((leftKanCanonicalCocone δ F (δ.app (Opposite.op ⦋0⦌) k)).leg
      (SSet.yonedaEquiv.symm (kanLeftKanIdentityVertex δ k))) := by
  let x := F.app (Opposite.op ⦋0⦌) (δ.app (Opposite.op ⦋0⦌) k)
  apply (isInvertibleEdge_congr (f := SSet.Truncated.Edge.id (X := (truncation 2).obj D) x) ?_).2
  · change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj D) x))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  · change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ _) = _
    rw [kanLeftCanonical_identity_restrict_val, SSet.comp_const]
    exact pinchedConstant_one x

/-- 概要：充満忠実な inner 包含の像では任意の関手の標準左 Kan 余錐が余極限。
方針：局所添字の恒等終対象へ制限すると定値な恒等余錐になる。
規約：関手 F が全ての点で Kan 条件を満たすとは仮定しない。
使われ方：一般の U 上で単位の像が可逆なとき局所の絶対余極限を回収する。 -/
lemma kanLeftCanonical_isColimit_at_image {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [InnerFibration δ] (hδ : IsFullyFaithful δ) (F : C ⟶ D) (k : K _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone δ F (δ.app (Opposite.op ⦋0⦌) k)) := by
  have := cofinalPointInclusion_mono (kanLeftKanIdentityVertex δ k)
  apply (isColimitCone_iff_restrict_of_rightAnodyne _
    (SSet.yonedaEquiv.symm (kanLeftKanIdentityVertex δ k))
    (SerrePositivity.InfinityCategories.F1B.terminalPoint_rightAnodyne (kanLeftKanIdentityVertex_isTerminal δ hδ k))).2
  apply isColimitCone_of_point_constant _ (F.app (Opposite.op ⦋0⦌) (δ.app (Opposite.op ⦋0⦌) k))
  exact kanLeftCanonical_identity_restrict_val δ F k

end SerrePositivity.InfinityCategories.F1B
