module

public import SerrePositivity.KST.Spectra.OriginalLoopModelMap
public import SerrePositivity.KST.Spectra.CotensorPost
public import SerrePositivity.KST.Spectra.TwistedKanSequenceNaturality
public import SerrePositivity.KST.Spectra.KanAdjointNaturality
public import SerrePositivity.KST.Spectra.PointedComponentIsomorphism
public import SerrePositivity.KST.Spectra.ComponentHomotopyMaps

/-!
概要：元のスペクトルから通常の loop 模型への実際の比較の自然性。
方針：符号を調整した Kan loop 列へ射影し、随伴の自然性で比較する。
規約：各段の成分と全整数次数の誘導準同型で自然性を述べる。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。有理化の単位の自然性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：符号を調整した Kan loop 列への比較は元の射に対して厳密に自然。
方針：cotensor の射影の比較と、符号反転と後合成の厳密な可換性を使う。
規約：射の左辺は通常の BF loop 模型間の実際の射。
使われ方：BF 1978 §2、HA §1.4.2。符号の補正を自然性から除く。 -/
theorem signedLoopRawComparison_post {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (tailMap (cotensorPost CirclePower.space.{u} f)).app n ≫
      (signedLoopRawComparison Y).app n =
    (signedLoopRawComparison X).app n ≫
      PointedObject.basedHomMap CirclePower.space.{u} (f.app (n + 1)) := by
  let r := KanSequence.tailHom (KanSequence.mappingPre
    (CirclePower.integerPowerMap.{u} (-1)) X.toKanSequence)
  let s := KanSequence.tailHom (KanSequence.mappingPre
    (CirclePower.integerPowerMap.{u} (-1)) Y.toKanSequence)
  let g := KanSequence.tailHom
    (KanSequence.mappingPost CirclePower.space.{u} (⟨f.app, f.comm⟩ :
      KanSequence.Hom X.toKanSequence Y.toKanSequence))
  have hg : ∀ k, r.app k ≫ g.app k = g.app k ≫ s.app k := by
    intro k
    change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _ _ ≫ (ihom CirclePower.space.{u}).map (f.app (k + 1)) =
      (ihom CirclePower.space.{u}).map (f.app (k + 1)) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _ _
    simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact MonoidalClosed.pre_comm_ihom_map _ _
  have hi := KanSequence.iterateHom_natural r s g hg n n
  change (cotensorPost CirclePower.space.{u} f).app (n + 1) ≫
      ((cotensorProjection CirclePower.space.{u} Y).app (n + 1) ≫
        (KanSequence.iterateHom s n).app n) =
    ((cotensorProjection CirclePower.space.{u} X).app (n + 1) ≫
        (KanSequence.iterateHom r n).app n) ≫ g.app n
  rw [← Category.assoc, cotensorPost_comparison]
  change ((cotensorProjection CirclePower.space.{u} X).app (n + 1) ≫ g.app n) ≫
    (KanSequence.iterateHom s n).app n = _
  simpa only [Category.assoc] using congrArg
    (fun h ↦ (cotensorProjection CirclePower.space.{u} X).app (n + 1) ≫ h) hi.symm

/-- 概要：元の対象から loop 模型への比較を符号付き Kan 列へ戻すと随伴と同じ成分。
方針：選んだ逆方向の BF 射の右ホモトピー逆を射影し、厳密化の成分保存を使う。
規約：各段の点つき写像空間での等式。
使われ方：BF 1978 §2、Goerss–Jardine I §7。実際の単位の自然性。 -/
theorem originalLoopModelMap_raw_component (X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.componentOf ((originalLoopModelMap X).app n ≫
      (signedLoopRawComparison X).app n) =
    PointedMapping.componentOf (KanSequence.kanAdjoint X.toKanSequence n) := by
  let e := signedLoopComparison X
  let g := levelwiseInverse e (signedLoopComparison_levelwise X)
  let v := (signedLoopUnit X).app n
  let p := (signedLoopProjection X).app n
  have h := PointedMapping.componentOf_comp_right
    (PointedMapping.componentOf_comp_left
      (levelwiseInverse_right_component e (signedLoopComparison_levelwise X) n) v) p
  have he : e.app n ≫ p = (signedLoopRawComparison X).app n :=
    signedLoopComparison_projection X n
  change PointedMapping.componentOf ((v ≫ (g.app n ≫ e.app n)) ≫ p) =
    PointedMapping.componentOf ((v ≫ 𝟙 _) ≫ p) at h
  change PointedMapping.componentOf ((v ≫ g.app n) ≫
    (signedLoopRawComparison X).app n) = _
  simpa only [Category.assoc, he, Category.comp_id] using
    h.trans (signedLoopUnit_projection_component X n)

/-- 概要：元の対象から通常の loop 模型への比較は各段の成分で自然。
方針：符号付き Kan 列への全基点 π_* 同型を打ち消し、随伴の自然性へ還元する。
規約：スペクトルの射そのものの厳密な可換性は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。有理化の模型の自然性。 -/
theorem originalLoopModelMap_natural_component {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    PointedMapping.componentOf (f.app n ≫ (originalLoopModelMap Y).app n) =
    PointedMapping.componentOf ((originalLoopModelMap X).app n ≫
      (tailMap (cotensorPost CirclePower.space.{u} f)).app n) := by
  apply PointedMapping.componentOf_cancel_post_piIsomorphism
    ((signedLoopRawComparison Y).app n) (signedLoopRawComparison_levelwise Y n)
  have hl := PointedMapping.componentOf_comp_left (originalLoopModelMap_raw_component Y n)
    (f.app n)
  have hr := PointedMapping.componentOf_comp_right (originalLoopModelMap_raw_component X n)
    (PointedObject.basedHomMap CirclePower.space.{u} (f.app (n + 1)))
  simpa only [Category.assoc, signedLoopRawComparison_post] using
    hl.trans ((KanSequence.kanAdjoint_natural
      (⟨f.app, f.comm⟩ : KanSequence.Hom X.toKanSequence Y.toKanSequence) n).trans hr.symm)

/-- 概要：元の対象から loop 模型への実際の比較は全整数次数の群準同型で自然。
方針：各段の成分での自然性を整数次数のホモトピー不変性へ移す。
規約：両辺は実際の BF 射の誘導準同型。
使われ方：BF 1978 §2、HA §1.4.2。有理化の単位の前段。 -/
theorem originalLoopModelMap_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) :
    homotopyMap (f ≫ originalLoopModelMap Y) j =
      homotopyMap (originalLoopModelMap X ≫ tailMap (cotensorPost CirclePower.space.{u} f)) j :=
  homotopyMap_eq_of_levelComponent (X := X) (Y := rationalizationModel Y)
    (f ≫ originalLoopModelMap Y)
    (originalLoopModelMap X ≫ tailMap (cotensorPost CirclePower.space.{u} f))
    (originalLoopModelMap_natural_component f) j

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
