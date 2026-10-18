module

public import SerrePositivity.KST.Comparison.HomologyMorphismProperty
public import SerrePositivity.KST.Comparison.HomologyHorn
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-!
# anodyne map の整数ホモロジー保存

概要：全ての anodyne map は正規化整数ホモロジー同型を誘導する。
方針：horn の同型性を余積、単射の pushout、超限合成、retract へ拡張する。
規約：Waldhausen LNM 1126 §1.7・§1.8 の Kan 置換の準備。局所係数の保存は別工程。
使われ方：セル添付後の Kan 置換の整数ホモロジー比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/--
概要：全ての horn 生成射は整数ホモロジー同型である。
方針：正次元 horn の実際の収縮による同型を適用する。
規約：Mathlib の J は全ての正次元と全ての horn を含む。
使われ方：小対象構成の生成射の計算。
-/
theorem hornGenerators_le_integralHomology :
    SSet.modelCategoryQuillen.J.{u} ≤ integralHomologyEquivalences := by
  rintro X Y f hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  exact (integralHomologyEquivalences_iff _).mpr (horn_integralHomologyIsomorphism i)

/--
概要：horn 生成射の余積の pushout は整数ホモロジー同型である。
方針：余積の単射性とホモロジー同型性を別々に導き、単射の pushout の定理を使う。
規約：全ての指定宇宙の添字集合。
使われ方：anodyne map のセル表示。
-/
theorem hornCellAttachments_le_integralHomology :
    (MorphismProperty.coproducts.{u} SSet.modelCategoryQuillen.J.{u}).pushouts ≤
      integralHomologyEquivalences := by
  have hmono : MorphismProperty.coproducts.{u} SSet.modelCategoryQuillen.J.{u} ≤
      MorphismProperty.monomorphisms SSet.{u} :=
    (MorphismProperty.coproducts_monotone SSet.modelCategoryQuillen.J_le_monomorphisms).trans
      (MorphismProperty.coproducts_le _)
  have hhom : MorphismProperty.coproducts.{u} SSet.modelCategoryQuillen.J.{u} ≤
      integralHomologyEquivalences :=
    (MorphismProperty.coproducts_monotone hornGenerators_le_integralHomology).trans
      (MorphismProperty.coproducts_le _)
  rintro X Y f ⟨A, B, p, l, r, hp, sq⟩
  have : Mono p := hmono p hp
  exact (integralHomologyEquivalences_iff f).mpr
    (integralHomologyIsomorphism_of_pushout sq.flip
      ((integralHomologyEquivalences_iff p).mp (hhom p hp)))

/--
概要：全ての anodyne map は整数ホモロジー同型である。
方針：小対象構成の horn セル表示と、ホモロジー同型の超限合成・retract の閉性を使う。
規約：存在する比較を追加公理として仮定しない。
使われ方：Kan 置換の整数ホモロジー保存。
-/
theorem anodyneExtensions_le_integralHomology :
    SSet.anodyneExtensions.{u} ≤ integralHomologyEquivalences := by
  rw [SSet.anodyneExtensions_eq_retracts_transfiniteCompositions,
    MorphismProperty.retracts_le_iff, MorphismProperty.transfiniteCompositions_le_iff]
  exact hornCellAttachments_le_integralHomology

/--
概要：anodyne map の全次数の整数ホモロジー誘導射は可逆である。
方針：射の性質による閉性の定理を通常のホモロジー条件へ戻す。
規約：正規化整数ホモロジーの実際の誘導射。
使われ方：Kan 模型の比較。
-/
theorem integralHomologyIsomorphism_of_anodyne {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.anodyneExtensions f) : IntegralHomologyIsomorphism f :=
  (integralHomologyEquivalences_iff f).mp (anodyneExtensions_le_integralHomology f hf)

end SerrePositivity.KST.Comparison
