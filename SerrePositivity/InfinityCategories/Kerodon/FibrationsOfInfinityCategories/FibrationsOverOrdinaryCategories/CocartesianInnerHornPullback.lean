module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.SubcomplexInverseImageComparison

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianNerveHornPullback

/-!
概要：標準単体上の cocartesian fibration の内ホーンの逆像は前合成同値。
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

/-- 概要：標準単体上の cocartesian fibration の内ホーンの逆像部分複体の包含は前合成同値。
方針：有限鎖の nerve 上の結果を、二つの逆像部分複体の等式で移す。
規約：全空間 E は任意の universe u の単体集合。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK） の生成ホーンの場合。 -/
lemma cocartesianFibration_innerHorn_preimage_isPrecompositionEquivalence
    (n : ℕ) (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n)
    {E : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence ((horn n k).preimage p).ι := by
  let e := stdSimplex.isoNerve.{u} n
  let q := p ≫ e.hom
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration e.hom := ⟨MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations e.hom⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q := inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (p ≫ e.hom))
  have h := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPrecompositionEquivalence_subcomplexInverseImage_iff q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn n k)).2
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_nerveHorn_pullback_isPrecompositionEquivalence n k h0 hn q)
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn n k).preimage q = (horn n k).preimage p := by
    change ((horn n k).preimage e.inv).preimage (p ≫ e.hom) = _
    rw [← Subcomplex.preimage_comp, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  rw [he] at h
  exact h

/-- 概要：内ホーンの cocartesian fibration に沿う pullback の射影は前合成同値。
方針：逆像部分複体から標準 pullback に移し、射影の順序を交換する。
規約：射影は元の全空間 E へ向かう第一射影。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK）、inner anodyne の生成ホーンの逆像。 -/
lemma cocartesianFibration_innerHorn_pullback_isPrecompositionEquivalence
    (n : ℕ) (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n)
    {E : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pullback.fst p (horn n k).ι) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPrecompositionEquivalence_subcomplexInverseImage_iff p (horn n k)).1
    (cocartesianFibration_innerHorn_preimage_isPrecompositionEquivalence n k h0 hn p)
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (pullbackSymmetry p (horn n k).ι)).comp h
  rw [pullbackSymmetry_hom_comp_snd] at hc
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.4.4.6" (partial := stronger-hyp) "仮定：標準単体と内ホーン、および単体への余デカルト・ファイブレーション（Lean が強い：指定の一辺だけでなく、射全体が余デカルト・ファイブレーション）。結論：内ホーン逆像の包含の前合成同値性と準圏間での準圏同値性（この場合に HA と一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_innerHorn_preimage_isPrecompositionEquivalence
attribute [cite HA "B.3.4" (partial := stronger-hyp) "仮定：p:X→∆2が全体でcoCartesian fibration（Leanが強い：各0頂点からmiddleへのcoCartesian liftだけでなく全辺のliftを仮定）。結論：inner horn Λ²₁の逆像包含は前合成同値、従ってcategorical equivalence（原典のflatnessの結論に一致）。原典の弱い片側lift仮定だけからの判定は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_innerHorn_pullback_isPrecompositionEquivalence
