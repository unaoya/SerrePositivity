module
public import SerrePositivity.KST.SConstruction.Cofinality.WideInternalFlags
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse

/-!
概要：同じ全多次数の wide 模型内で ambient 可逆辺の可逆性を回収する。
方針：ambient core の全辺が分母に属することから core 全体を wide へ持ち上げる。
規約：wide 包含の充満忠実性は仮定しない。
使われ方：内部旗と相対旗の core 比較の逆方向。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：同じ標的の ambient core は元の wide 模型を経由する。
方針：core の任意の一次制限の可逆性に cofiber 像条件を適用する。
規約：全高次単体を保持した持ち上げ。
使われ方：ambient 可逆辺を wide 内の可逆辺として読む。 -/
def completionAmbientCoreToWide (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (((multiSEndofunctor r).obj ι).obj Y).carrier : SSet.{u}) ⟶
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) :=
  Subcomplex.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore _).ι (by
    intro n s hs
    obtain ⟨t, rfl⟩ := hs
    intro θ
    exact completionMulti_invertibleEdge_mem r ι f hf _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
        (((multiSEndofunctor r).obj ι).obj Y).carrier : SSet.{u}).map θ.op t)))

/-- 概要：wide の辺が元の標的で可逆なら wide 内でも可逆である。
方針：元の辺を ambient core の辺として読み、core の Kan 性から可逆性を写す。
規約：分母辺の全てを可逆と仮定しない。
使われ方：相対 core 旗の可逆変換の内部 wide への反映。 -/
lemma completionWide_invertibleEdge_of_ambient (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) _⦋1⦌)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a.val)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a) := by
  let b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (((multiSEndofunctor r).obj ι).obj Y).carrier : SSet.{u}) _⦋1⦌ :=
    ⟨a.val, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff a.val).mpr ha⟩
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex b) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)
  have hm := hb.map (completionAmbientCoreToWide r ι f hf)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex b).map
    ((truncation 2).map (completionAmbientCoreToWide r ι f hf)))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a) rfl).mp hm

end SerrePositivity.KST.SConstruction.Cofinality
