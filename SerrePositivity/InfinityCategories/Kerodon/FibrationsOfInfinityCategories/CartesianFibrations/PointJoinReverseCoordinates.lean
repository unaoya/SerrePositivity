module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberCoordinates

/-!
概要：点と任意の標準単体の join の反転を標準単体の反転と照合する。
方針：標準単体の自己同型が恒等であることから、二つの標準表示の同型を同定する。
規約：全次数で成り立つ厳密な等式。有限個の面への制限は用いない。
使われ方：反転した右 slice と左 pinched Hom の共通の単体表示。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 標準単体の自己同型は恒等。単体圏の自己同型の一意性を Yoneda で移す。 -/
lemma stdSimplexAutomorphism_eq_refl (n : ℕ) (e : (Δ[n] : SSet.{u}) ≅ Δ[n]) :
    e = Iso.refl _ := by
  calc
    e = stdSimplex.mapIso (stdSimplex.fullyFaithful.preimageIso e) :=
      (stdSimplex.fullyFaithful.isoEquiv.apply_symm_apply e).symm
    _ = Iso.refl _ := by
      rw [SimplexCategory.iso_eq_iso_refl (stdSimplex.fullyFaithful.preimageIso e)]
      exact Functor.mapIso_refl _ _

/-- 標準単体への二つの同型は一致する。 -/
lemma stdSimplexIso_unique {X : SSet.{u}} (n : ℕ) (e f : X ≅ Δ[n]) : e = f := by
  apply Iso.ext
  apply (cancel_epi e.inv).1
  have h := congrArg Iso.hom (stdSimplexAutomorphism_eq_refl n (e.symm ≪≫ f))
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id, Iso.refl_hom] using h.symm

/-- 右に点を付けた標準単体の反転は、左に点を付けた標準表示と一致する。 -/
lemma pointJoinReverseIso_coordinates (n : ℕ) :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} n 0).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[n] Δ[0]).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).hom (stdSimplex.opIso ⦋n⦌).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom = (stdSimplex.opIso ⦋n + 1⦌).hom := by
  let e := SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} n 0).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[n] Δ[0] ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (stdSimplex.opIso ⦋0⦌) (stdSimplex.opIso ⦋n⦌) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n
  exact congrArg Iso.hom (stdSimplexIso_unique (n + 1) e (stdSimplex.opIso ⦋n + 1⦌))

/-- 同じ join の反転の逆方向は、元の右点表示の後で標準単体を反転する。 -/
lemma pointJoinReverseIso_inv_coordinates (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (stdSimplex.opIso ⦋n⦌).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[n] Δ[0]).inv ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} n 0).hom =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom ≫ (stdSimplex.opIso ⦋n + 1⦌).inv := by
  let e := SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} n 0).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[n] Δ[0] ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (stdSimplex.opIso ⦋0⦌) (stdSimplex.opIso ⦋n⦌) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n
  have he : e = stdSimplex.opIso ⦋n + 1⦌ := Iso.ext (pointJoinReverseIso_coordinates n)
  have h := congrArg (fun i ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso.{u} n).hom ≫ i.inv) he
  dsimp only [e, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso] at h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
