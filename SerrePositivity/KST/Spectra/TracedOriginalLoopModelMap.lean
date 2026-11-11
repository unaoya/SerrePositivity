module

public import SerrePositivity.KST.Spectra.TracedSignedLoopUnit
public import SerrePositivity.KST.Spectra.OriginalLoopModelMap
public import SerrePositivity.KST.Spectra.SpectrumLevelwiseInversePostInterval

/-!
概要：トレースを保持した単位を使う、元のスペクトルから通常の loop 模型への実比較。
方針：同じ選択済み逆比較を後合成し、その右逆の全 Hom 区間も保持する。
規約：従来の単位とのホモトピーを仮定しない。使われ方：実評価の源比較の選択。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open RawSpectrumMapping

/-- 実構造区間を保持する単位から、同じ通常の BF loop 模型へ送る。 -/
def tracedOriginalLoopModelMap (X : OmegaSpectrum.{u}) : X ⟶ rationalizationModel X :=
  tracedSignedLoopUnit X ≫
    levelwiseInverse (signedLoopComparison X) (signedLoopComparison_levelwise X)

/-- 同じ源比較は全段・全基点で π 同型。 -/
lemma tracedOriginalLoopModelMap_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((tracedOriginalLoopModelMap X).app n).right :=
  (tracedSignedLoopUnit_levelwise X n).comp
    (levelwiseInverse_levelwise (signedLoopComparison X) (signedLoopComparison_levelwise X) n)

/-- 源比較を同じ BF 比較へ戻すと、全 Hom 上でトレース付き単位まで実際に変形する。 -/
def tracedOriginalLoopModelMap_unit_post_interval (A X : OmegaSpectrum.{u}) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (pointedSpace A (signedLoopModel X).toKanSequence))
      (pointedPost A (sequenceHom (tracedOriginalLoopModelMap X)) ≫
        pointedPost A (sequenceHom (signedLoopComparison X)))
      (pointedPost A (sequenceHom (tracedSignedLoopUnit X))) := by
  let v := pointedPost A (sequenceHom (tracedSignedLoopUnit X))
  let g := pointedPost A (sequenceHom
    (levelwiseInverse (signedLoopComparison X) (signedLoopComparison_levelwise X)))
  let e := pointedPost A (sequenceHom (signedLoopComparison X))
  have hv : v ≫ g = pointedPost A (sequenceHom (tracedOriginalLoopModelMap X)) :=
    pointedPost_comp_eq A (sequenceHom (tracedSignedLoopUnit X))
      (sequenceHom (levelwiseInverse (signedLoopComparison X) (signedLoopComparison_levelwise X)))
      (sequenceHom (tracedOriginalLoopModelMap X)) (fun _ => rfl)
  have ha : pointedPost A (sequenceHom (tracedOriginalLoopModelMap X)) ≫ e = v ≫ (g ≫ e) := by
    rw [← hv, Category.assoc]
  exact ((levelwiseInverse_post_right_interval A (signedLoopComparison X)
    (signedLoopComparison_levelwise X)).pre v).changeEndpoints ha (Category.comp_id v).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum
