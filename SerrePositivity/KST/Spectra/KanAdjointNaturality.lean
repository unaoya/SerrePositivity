module

public import SerrePositivity.KST.Spectra.SignedLoopModel
public import SerrePositivity.KST.Spectra.PointedComponentCancellation

/-!
概要：Kan 円への随伴構造射の持ち上げは点つき射の成分で自然。
方針：通常の円への制限の全単射 RLP で持ち上げの選択を打ち消す。
規約：成分での自然性を述べ、選択の厳密な可換性は要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。有理化の単位の自然性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 円への随伴構造射は厳密な Kan 列の射に対して成分で自然。
方針：通常の円へ制限すると随伴の厳密な自然性となる。
規約：始域と終域は Kan 列、Ω 条件を要しない。
使われ方：BF 1978 §2、Goerss–Jardine I §7。単位の自然性の局所計算。 -/
theorem KanSequence.kanAdjoint_natural {X Y : KanSequence.{u}} (f : Hom X Y) (n : ℕ) :
    PointedMapping.componentOf (f.app n ≫ kanAdjoint Y n) =
      PointedMapping.componentOf (kanAdjoint X n ≫
        PointedObject.basedHomMap CirclePower.space.{u} (f.app (n + 1))) := by
  apply PointedMapping.componentOf_eq_of_comp_eq_rlp
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (Y.level (n + 1)).space)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp CirclePower.unit
      (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) _)
  rw [Category.assoc, kanAdjoint_comparison]
  change _ = kanAdjoint X n ≫ ((ihom CirclePower.space.{u}).map (f.app (n + 1)) ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (Y.level (n + 1)).space)
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    ← MonoidalClosed.pre_comm_ihom_map, ← Category.assoc]
  have hc := kanAdjoint_comparison X n
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hc
  rw [hc]
  exact f.adjoint_comm n

/-- 概要：符号を調整した BF loop 模型への単位は随伴構造射の成分を持つ。
方針：厳密化の射影式と各段の成分保存を使う。
規約：標的は単射置換前の実際の Kan loop 列。
使われ方：BF 1978 §2、HTT A.3.3。有理化の単位と随伴の接続。 -/
theorem OmegaSpectrum.signedLoopUnit_projection_component (X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.componentOf ((signedLoopUnit X).app n ≫ (signedLoopProjection X).app n) =
      PointedMapping.componentOf (KanSequence.kanAdjoint X.toKanSequence n) := by
  have hp := OmegaSpectrum.rectifyInto_projection X
    (KanSequence.signedLoopTail X.toKanSequence)
    (KanSequence.signedLoopTail_omegaCondition X.toKanSequence_omega)
    (KanSequence.kanAdjoint X.toKanSequence)
    (KanSequence.kanAdjoint_signedLoopTail_comm X.toKanSequence_omega) n
  change (signedLoopUnit X).app n ≫ (signedLoopProjection X).app n = _ at hp
  rw [hp]
  exact KanSequence.rectify_component (X := X.toKanSequence)
    (Y := KanSequence.signedLoopTail X.toKanSequence) X.sigma_mono _ _ n

end

end SerrePositivity.KST.Spectra
