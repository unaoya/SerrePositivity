module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawPureCoordinates
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents
/-!
概要：貼り合わせた join 単体データの左右への制限は指定データに一致する。
方針：頂点族と全部分集合の成分をそれぞれ比較する。
規約：単体方程式を仮定しない。
使われ方：逆比較の純粋な面と自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

lemma dgCoherentBarJoinRawData_left {n m : ℕ}
    (s : SimplexData R C n) (t : SimplexData R C m) (f : DGCoherentBarJoinMixedData s t) :
    (dgCoherentBarJoinRawData s t f).pullback (dgCoherentBarJoinLeft n m) = s := by
  have hObj : ((dgCoherentBarJoinRawData s t f).pullback
      (dgCoherentBarJoinLeft n m)).obj = s.obj := by
    funext i
    exact dgCoherentBarJoinObjects_left s.obj t.obj i
  apply SimplexData.ext hObj
  apply HomFamily.heq_of_pointwise hObj
  intro K a b k hK ha hb hk
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    (dgCoherentBarJoinLeft_injective n m).injOn]
  simpa only [dgCoherentBarJoinSubset, Finset.image_empty, Finset.union_empty] using
    dgCoherentBarJoinRawData_left_hom_heq s t f K a b k hK ha hb hk

lemma dgCoherentBarJoinRawData_right {n m : ℕ}
    (s : SimplexData R C n) (t : SimplexData R C m) (f : DGCoherentBarJoinMixedData s t) :
    (dgCoherentBarJoinRawData s t f).pullback (dgCoherentBarJoinRight n m) = t := by
  have hObj : ((dgCoherentBarJoinRawData s t f).pullback
      (dgCoherentBarJoinRight n m)).obj = t.obj := by
    funext i
    exact dgCoherentBarJoinObjects_right s.obj t.obj i
  apply SimplexData.ext hObj
  apply HomFamily.heq_of_pointwise hObj
  intro L a b k hL ha hb hk
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    (dgCoherentBarJoinRight_injective n m).injOn]
  simpa only [dgCoherentBarJoinSubset, Finset.image_empty, Finset.empty_union] using
    dgCoherentBarJoinRawData_right_hom_heq s t f L a b k hL ha hb hk

end SerrePositivity.InfinityCategories
