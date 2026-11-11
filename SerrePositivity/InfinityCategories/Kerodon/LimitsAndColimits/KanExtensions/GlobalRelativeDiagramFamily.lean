module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.GlobalDiagramFamilyEquiv
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseRelativeRestriction

/-!
概要：指定された元の図式と標的の全図式から相対比較の標的の大域的な族を作る。
方針：大域図式の族の後合成の自然性と制限の自然性で引き戻しへ合わせる。
規約：充填性を仮定しない。
使われ方：局所相対余錐から coherent な族を選ぶ際の固定された標的。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：大域図式の後合成はその fiber ごとの族の後合成と一致する。
方針：恒等射に沿う逆像の第二射影への合成と curry の自然性を照合する。
規約：標的の射は任意。
使われ方：相対比較の標的の大域的な族の可換性。 -/
lemma kanGlobalDiagramFamily_postcomp {K C D E : SSet.{u}}
    (p : K ⟶ C) (U : D ⟶ E) (F : K ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily p (F ≫ U) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily p F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp p U := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_postcomp]
  congr 1

/-- 概要：元の図式と標的の全図式を合わせた相対比較の標的の族。
方針：後合成と制限の自然性で大域図式の族を引き戻しへ合わせる。
規約：hFU は左端での二つの指定の厳密な一致。
使われ方：各底頂点で選ぶ局所相対余錐の像の指定。 -/
def kanGlobalRelativeDiagramFamily {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) (F : K.left ⟶ D) (H₀ : L.left ⟶ E)
    (hFU : F ≫ U = i.left ≫ H₀) : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseRelativeTarget i U :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily K.hom F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily L.hom H₀)
    (by rw [← kanGlobalDiagramFamily_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily_pre, hFU])

/-- 概要：相対標的の大域的な族の第一成分は元の図式の族。
方針：引き戻しの第一射影を計算する。
規約：底上の射 i は任意。
使われ方：相対始対象の頂点の第一成分の同定。 -/
lemma kanGlobalRelativeDiagramFamily_fst {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) (F : K.left ⟶ D) (H₀ : L.left ⟶ E)
    (hFU : F ≫ U = i.left ≫ H₀) :
    kanGlobalRelativeDiagramFamily i U F H₀ hFU ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp K.hom U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := E) i) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily K.hom F := pullback.lift_fst _ _ _

/-- 概要：相対標的の大域的な族の第二成分は標的の全図式の族。
方針：引き戻しの第二射影を計算する。
規約：標的での全図式を保持する。
使われ方：相対始対象の頂点の第二成分の同定。 -/
lemma kanGlobalRelativeDiagramFamily_snd {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) (F : K.left ⟶ D) (H₀ : L.left ⟶ E)
    (hFU : F ≫ U = i.left ≫ H₀) :
    kanGlobalRelativeDiagramFamily i U F H₀ hFU ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp K.hom U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := E) i) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily L.hom H₀ := pullback.lift_snd _ _ _

/-- 概要：相対標的の大域的な族は底の恒等射上にある。
方針：第一成分の式と大域図式の族の射影の式を合成する。
規約：底を厳密に固定する。
使われ方：選択した族を大域図式へ戻す。 -/
lemma kanGlobalRelativeDiagramFamily_projection {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) (F : K.left ⟶ D) (H₀ : L.left ⟶ E)
    (hFU : F ≫ U = i.left ≫ H₀) :
    kanGlobalRelativeDiagramFamily i U F H₀ hFU ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseRelativeProjection i U = 𝟙 C := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseRelativeProjection, ← Category.assoc, kanGlobalRelativeDiagramFamily_fst,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily_projection]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
