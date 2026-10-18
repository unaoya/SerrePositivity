module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# 部分単体集合の既存の束の分配性

概要：Mathlib の部分単体集合の既存の束の演算に分配法則を証明する。
方針：各次数の集合の和・交叉の命題を場合分けする。
規約：Segal 1974 Proposition 1.6 の有限被覆の束の帰納。既存の演算を取り替えない。
使われ方：有限交叉の局所条件から有限和への帰納。
-/

@[expose] public section
universe u
namespace SerrePositivity.KST.Comparison

/--
概要：部分単体集合の既存の和・交叉は分配束をなす。
方針：各次数で二つの和への所属を場合分けし、集合の分配法則を使う。
規約：親の Lattice は既存の CompleteLattice からそのまま取る。
使われ方：境界の面の有限被覆の帰納。
-/
instance subcomplexDistribLattice (K : SSet.{u}) : DistribLattice K.Subcomplex where
  toLattice := inferInstance
  le_sup_inf U V W d x hx := by
    rcases hx with ⟨hU | hV, hU' | hW⟩
    · exact Or.inl hU
    · exact Or.inl hU
    · exact Or.inl hU'
    · exact Or.inr ⟨hV, hW⟩

end SerrePositivity.KST.Comparison
