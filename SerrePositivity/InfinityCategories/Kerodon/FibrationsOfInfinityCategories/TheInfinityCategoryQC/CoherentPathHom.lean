module

public import Mathlib.AlgebraicTopology.SimplicialNerve

/-!
概要：thickening の path の精密化の一意性。
方針：誘導された圏の射の三つの包みを外して包含の証明を比較する。
規約：射の存在や path の等号は仮定しない。
使われ方：coherent な三角形・四面体の面の比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：同じ二つの path の間の精密化の射は一意。
方針：誘導された圏の射を集合の包含へ戻し、命題の証明の無関係性を使う。
規約：任意の線型順序と任意の端点を扱う。
使われ方：三単体の四面の指定辺を標準の精密化と同定する。 -/
lemma coherentPathHom_ext {J : Type u} [LinearOrder J] {i j : J}
    {P Q : SimplicialThickening.Path i j} (f g : P ⟶ Q) : f = g := by
  apply InducedCategory.hom_ext
  apply ULift.ext
  apply Subsingleton.elim

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
