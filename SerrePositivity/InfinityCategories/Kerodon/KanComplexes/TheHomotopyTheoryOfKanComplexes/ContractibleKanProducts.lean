module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! # 可縮 Kan 複体の積
概要：独立な二つの可縮な選択を同じパラメーターで同時に補完する。
方針：二つの射影の境界をそれぞれ埋め、直積へ戻す。
規約：零次元と全ての高次の既存部分を保つ。
使われ方：比較逆射と Kan 延長の同時選択。

対応節は Kerodon 3.1（Tag 00SZ）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 可縮 Kan 複体の直積も全ての境界を充填する。 -/
lemma contractibleKan_tensor {K L : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K)
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan L) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (K ⊗ L) := by
  intro n a
  obtain ⟨f, hf⟩ := hK n (a ≫ fst K L)
  obtain ⟨g, hg⟩ := hL n (a ≫ snd K L)
  refine ⟨lift f g, ?_⟩
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro v
  apply Prod.ext
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hf d) v
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hg d) v

/-- 可縮な積のパラメーター族を任意の単射に沿い相対的に補完できる。 -/
lemma contractibleKan_tensor_relative_lifting {K L : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K)
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan L) {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ K ⊗ L) :
    ∃ b : T ⟶ K ⊗ L, j ≫ b = a := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration _).1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.contractibleKan_tensor hK hL)
  have := hc.mem j inferInstance
  let sq : CommSq a j (terminal.from (K ⊗ L)) (terminal.from T) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
