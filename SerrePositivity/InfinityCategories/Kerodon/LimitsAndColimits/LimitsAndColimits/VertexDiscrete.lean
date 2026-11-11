module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap

/-!
概要：単体集合の全頂点からなる定値単体集合とその包含。
方針：各次数で零単体の型を取り、頂点の定値単体として元へ写す。
規約：異なる頂点は全次数で区別する。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の点ごとの極限から自然な錐の構成。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：単体集合の頂点を対象とする離散的な単体集合。
方針：各次数で同じ頂点の型を取り、単体作用を恒等写像にする。
規約：元の単体集合と同じ宇宙。
使われ方：Kerodon §7.1.8（Tag 02X8） の零骨格上の選択。 -/
def vertexDiscrete (A : SSet.{u}) : SSet.{u} where
  obj _ := A _⦋0⦌
  map _ := 𝟙 _

/-- 概要：離散的な頂点の単体集合を元の単体集合へ含める。
方針：各次数で頂点の定値単体へ写す。
規約：零次成分は恒等写像。
使われ方：Kerodon §7.1.8（Tag 02X8） の頂点で選んだ錐の延長。 -/
def vertexDiscreteι (A : SSet.{u}) : vertexDiscrete A ⟶ A where
  app d := ↾fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x d.unop.len
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback x α.unop).symm

/-- 概要：離散的な頂点の包含は単射。
方針：定値単体を最初の頂点へ制限して元の頂点を回収する。
規約：元の単体集合に追加の仮定は不要。
使われ方：Kerodon §7.1.8（Tag 02X8） の相対骨格の適用。 -/
instance vertexDiscreteι_mono (A : SSet.{u}) : Mono (vertexDiscreteι A) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro x y h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n at h
  have hh := congrArg (A.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op) h
  have hx : A.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n) = x :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback (X := A) x (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero (X := A) x)
  have hy : A.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n) = y :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback (X := A) y (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero (X := A) y)
  exact hx.symm.trans (hh.trans hy)

/-- 概要：各頂点に選んだ像を離散的な頂点の単体集合上の射にする。
方針：各次数で選んだ頂点の定値単体へ写す。
規約：選んだ像の間の自然性は要求しない。
使われ方：Kerodon §7.1.8（Tag 02X8） の点ごとの極限錐の零骨格上の選択。 -/
def vertexDiscreteMap {A E : SSet.{u}} (x : A _⦋0⦌ → E _⦋0⦌) : vertexDiscrete A ⟶ E where
  app d := ↾fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x a) d.unop.len
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback (x a) α.unop).symm

/-- 概要：各頂点で基底と可換な選択は離散的な頂点上でも基底と可換。
方針：射が定値単体を定値単体へ写すことを使う。
規約：元の射のファイブレーション性は不要。
使われ方：Kerodon §7.1.8（Tag 02X8） の錐の制限の持ち上げの零骨格。 -/
lemma vertexDiscreteMap_comp {A E B : SSet.{u}} (p : E ⟶ B) (g : A ⟶ B)
    (x : A _⦋0⦌ → E _⦋0⦌)
    (hx : ∀ v, p.app (Opposite.op ⦋0⦌) (x v) = g.app (Opposite.op ⦋0⦌) v) :
    vertexDiscreteMap x ≫ p = vertexDiscreteι A ≫ g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro v
  change p.app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x v) n) =
    g.app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v n)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, hx]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
