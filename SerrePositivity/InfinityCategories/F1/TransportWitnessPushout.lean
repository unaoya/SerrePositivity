module

public import SerrePositivity.InfinityCategories.F1.TransportWitnessDescentLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：底上の pushout を実際の表現空間の pullback に写す。
方針：反対圏の pullback と表現空間の極限保存を使う。
規約：貼り合わせの単射性や表現の存在は仮定しない。
使われ方：標準単体のセル分解に沿う表現の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の pushout は実際の表現空間の厳密な pullback を与える。
方針：pushout の反対の pullback を極限を保つ反変関手で写す。
規約：全ての高次単体の貼り合わせを含む。
使われ方：境界とセルの表現を貼り合わせる帰納法。 -/
lemma transportWitnessPullbackFunctor_map_pushout {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] {a x y z : Over B}
    {f : a ⟶ x} {g : a ⟶ y} {h : x ⟶ z} {i : y ⟶ z}
    (hs : IsPushout f g h i) :
    IsPullback ((transportWitnessPullbackFunctor p).map h.op)
      ((transportWitnessPullbackFunctor p).map i.op)
      ((transportWitnessPullbackFunctor p).map f.op)
      ((transportWitnessPullbackFunctor p).map g.op) :=
  hs.op.flip.map (transportWitnessPullbackFunctor p)

end SerrePositivity.InfinityCategories
