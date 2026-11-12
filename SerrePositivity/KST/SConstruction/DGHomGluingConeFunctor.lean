module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeHomUnit
public import SerrePositivity.KST.SConstruction.DGHomGluingConeHomComposition

/-! # 元の比較 cone の実 dg 関手
概要：元の実 Perf cone 対象族と、第三比較を保持する全 Hom 鎖写像を dg 関手にする。
方針：元の単位と全次数の豊穣合成の保存を直接束ねる。
規約：厳密 dg 入力の全 Hom を保持。使われ方：D β3 の指定収縮と商延長への接続。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)

/-- 元の比較の実 cone へ送る、第三成分を保持した全 Hom 上の厳密 dg 関手。 -/
def dgHomGluingConeFunctor :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
      (PerfectDGModule R E) :=
  DGFunctor.ofHomMaps R (dgHomGluingTargetCone R C D E p q)
    (dgHomGluingConeHomMap R C D E p q) (dgHomGluingConeHomMap_unit R C D E p q)
    (fun X Y Z r s n hn a b => dgHomGluingConeHomMap_forward R C D E p q X Y Z
      (r := r) (s := s) (n := n) hn a b)

/-- 同じ実 dg 関手の対象は元の実 Perf cone そのもの。 -/
lemma dgHomGluingConeFunctor_obj
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) :
    (dgHomGluingConeFunctor R C D E p q).obj X =
      dgHomGluingTargetCone R C D E p q X := rfl

/-- 同じ実 dg 関手の全 Hom 作用は元の第三比較を保持する同じ鎖写像。 -/
lemma dgHomGluingConeFunctor_map
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) :
    (dgHomGluingConeFunctor R C D E p q).map X Y =
      dgHomGluingConeHomMap R C D E p q X Y := rfl

end SerrePositivity.KST.SConstruction
