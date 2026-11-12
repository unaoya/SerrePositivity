module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateFaces
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomotopyImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarFaceDifferential
/-!
概要：退化単体の非例外面の正規化像は零で、同じ面ラベルの係数は一致する。
方針：退化標的への全 Hom の消滅と、D の同じ単位 shift ブロックへの異種等号を使う。
規約：同じ theta の係数と端点輸送を保持し、既存の係数証明をコピーしない。
使われ方：退化部分の保存と段階的正規化で必要な例外二面の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarPostInclusion_eq_of_heq (s t t' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) (h : t = t') (q : ℤ)
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F t))).X q)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F t'))).X q)
    (hfg : HEq f g) :
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) t)).f q f =
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) t')).f q g := by
  cases h
  cases hfg
  rfl

set_option maxHeartbeats 800000 in
-- 元の Hom end と二つの端点輸送の照合だけに elaboration 上限を増やす。
lemma dgCoherentBarFaceColumn_eq_of_label_eq {n : ℕ} (s : I _⦋n + 1⦌)
    (i j : Fin (n + 1)) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s j.succ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F s i = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F s j :=
  dgCoherentBarPostInclusion_eq_of_heq R D F ⟨n + 1, s⟩
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s j.succ) h 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s i) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s j)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock_heq R D F s i).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock_heq R D F s j).symm)

set_option maxHeartbeats 800000 in
-- 正規化直和の全 Hom end を単体ラベル付き係数へ照合する。
lemma dgCoherentBarFaceColumn_degenerate_normalizedProjection {n : ℕ}
    (s : I _⦋n⦌) (j : Fin (n + 1)) (i : Fin (n + 1))
    (h₁ : i.succ ≠ j.castSucc) (h₂ : i.succ ≠ j.succ) :
    (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, I.σ j s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F)).f 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ j s) i) = 0 :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateTargetColumn_normalizedProjection R D F ⟨n + 1, I.σ j s⟩
    ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace (I.σ j s) i.succ, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_face_degenerate s j i.succ h₁ h₂⟩
    1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F (I.σ j s) i)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
