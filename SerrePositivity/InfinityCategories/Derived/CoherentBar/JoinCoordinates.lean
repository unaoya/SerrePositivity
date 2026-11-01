module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeCoordinates
public import SerrePositivity.InfinityCategories.Core.JoinSimplexInclusions
/-!
概要：高次余錐族の混合単体に使う、二つの標準単体の join の左右の座標。
方針：既存 DGNerve の左右の包含とその同型の公式を直接再利用する。
規約：元の図式とパラメーターの順序を保ち、頂点の反転を加えない。
使われ方：混合 HA 成分の始域と終域の固定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

abbrev dgCoherentBarJoinLeft (n m : ℕ) := DGNerve.joinLeftOrderHom n m

abbrev dgCoherentBarJoinRight (n m : ℕ) := DGNerve.joinRightOrderHom n m

lemma dgCoherentBarJoinLeft_inl (n m : ℕ) :
    joinInl (Δ[n] : SSet.{u}) Δ[m] ≫ (joinStdSimplexIso n m).hom =
      SSet.stdSimplex.map (SimplexCategory.mkHom (dgCoherentBarJoinLeft n m)) :=
  DGNerve.joinStdSimplexIso_inl n m

lemma dgCoherentBarJoinRight_inr (n m : ℕ) :
    joinInr (Δ[n] : SSet.{u}) Δ[m] ≫ (joinStdSimplexIso n m).hom =
      SSet.stdSimplex.map (SimplexCategory.mkHom (dgCoherentBarJoinRight n m)) :=
  DGNerve.joinStdSimplexIso_inr n m

end SerrePositivity.InfinityCategories
