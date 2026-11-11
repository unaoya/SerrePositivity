module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLift
public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClassFunctor
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic

/-!
概要：宇宙持ち上げは inner anodyne な包含を保つ。
方針：標準内ホーンの持ち上げの同型と生成された左クラスの余極限保存を使う。
規約：モデル構造の存在を仮定しない。
使われ方：同じ部分底の native Hom と分類先 Hom の自明 Kan 制限の宇宙を揃える。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 内ホーン生成射の宇宙持ち上げは、同じ番号の内ホーンの同型で inner anodyne。 -/
lemma innerHornInclusions_ulift_map : innerHornInclusions.{u} ≤
    innerAnodyneExtensions.{max u v}.inverseImage (SSet.uliftFunctor.{v, u}) := by
  intro X Y f hf
  obtain @⟨n, i, h0, hn⟩ := hf
  exact (innerAnodyneExtensions.arrow_mk_iso_iff
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornArrowIso.{v, u} (n + 2) i)).mpr
      (innerAnodyneExtensions.horn_ι h0 hn)

/-- 任意の inner anodyne 射を、同じ射の宇宙持ち上げとして保つ。 -/
lemma innerAnodyneExtensions_ulift_map {A B : SSet.{u}} (i : A ⟶ B)
    (hi : innerAnodyneExtensions i) :
    innerAnodyneExtensions ((SSet.uliftFunctor.{v, u}).map i) := by
  rw [innerAnodyneExtensions_eq_llp_rlp] at hi
  exact ModelGeneration.generatedLeft_map (SSet.uliftFunctor.{v, u})
    innerAnodyneExtensions innerHornInclusions innerHornInclusions_ulift_map i hi

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
