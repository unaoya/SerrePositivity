module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.SubcomplexInverseImageComparison

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ReplacementInnerHornPullback

/-!
概要：標準単体上の left fibration の内ホーンの逆像は前合成同値。
方針：底を有限鎖の nerve へ移し、逆像部分複体の等式で比較を戻す。
規約：モデル構造や平坦性を仮定しない。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK）、一般の inner anodyne 射の生成元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：標準単体上の left fibration の内ホーンの逆像部分複体の包含は前合成同値。
方針：有限鎖の nerve 上の結果を、二つの逆像部分複体の等式で移す。
規約：全空間 E は任意の universe u の単体集合。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK） の生成ホーンの場合。 -/
lemma leftFibration_innerHorn_preimage_isPrecompositionEquivalence
    (n : ℕ) (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n)
    {E : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence ((horn n k).preimage p).ι := by
  let e := stdSimplex.isoNerve.{u} n
  let q := p ≫ e.hom
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))
    (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations e.hom)⟩
  have h := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPrecompositionEquivalence_subcomplexInverseImage_iff q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn n k)).2
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibration_nerveHorn_pullback_isPrecompositionEquivalence n k h0 hn q)
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn n k).preimage q = (horn n k).preimage p := by
    change ((horn n k).preimage e.inv).preimage (p ≫ e.hom) = _
    rw [← Subcomplex.preimage_comp, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  rw [he] at h
  exact h

/-- 概要：内ホーンの left fibration に沿う pullback の射影は前合成同値。
方針：逆像部分複体から標準 pullback に移し、射影の順序を交換する。
規約：射影は元の全空間 E へ向かう第一射影。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK）、inner anodyne の生成ホーンの逆像。 -/
lemma leftFibration_innerHorn_pullback_isPrecompositionEquivalence
    (n : ℕ) (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n)
    {E : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pullback.fst p (horn n k).ι) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPrecompositionEquivalence_subcomplexInverseImage_iff p (horn n k)).1
    (leftFibration_innerHorn_preimage_isPrecompositionEquivalence n k h0 hn p)
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (pullbackSymmetry p (horn n k).ι)).comp h
  rw [pullbackSymmetry_hom_comp_snd] at hc
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
