module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLiftedCoordinateIdentities

/-!
概要：大きいパラメーター上の Hom 族を、有限 path の元の小さい Hom へ戻す。
方針：有限標準単体の座標を持ち上げ、完全忠実な ulift の逆像を取る。
規約：対象の宇宙と豊穣 Hom の宇宙を混同しない。
使われ方：元の二短辺の作用と、新しい長 Hom の作用の同じ宇宙での照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

def triangleLiftedHom {A H : SSet.{u}} {K : SSet.{max u v}} {n : ℕ}
    (c : A ⟶ (Δ[n] : SSet.{u})) (s : K _⦋n⦌)
    (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj H) : A ⟶ H :=
  (SSet.uliftFunctor.{v, u}).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate c s ≫ f)

lemma triangleLiftedHom_map {A H : SSet.{u}} {K : SSet.{max u v}} {n : ℕ}
    (c : A ⟶ (Δ[n] : SSet.{u})) (s : K _⦋n⦌)
    (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj H) :
    (SSet.uliftFunctor.{v, u}).map (triangleLiftedHom c s f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate c s ≫ f :=
  (SSet.uliftFunctor.{v, u}).map_preimage _

lemma triangleLiftedHom_precomp {A B H : SSet.{u}} {K : SSet.{max u v}} {n : ℕ}
    (i : A ⟶ B) (c : B ⟶ (Δ[n] : SSet.{u})) (s : K _⦋n⦌)
    (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj H) :
    i ≫ triangleLiftedHom c s f = triangleLiftedHom (i ≫ c) s f := by
  apply (SSet.uliftFunctor.{v, u}).map_injective
  rw [Functor.map_comp, triangleLiftedHom_map, triangleLiftedHom_map,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate_precomp]

lemma triangleLiftedHom_naturality {A H : SSet.{u}} {K : SSet.{max u v}} {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (c : A ⟶ (Δ[m] : SSet.{u})) (s : K _⦋n⦌)
    (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj H) :
    triangleLiftedHom (c ≫ stdSimplex.map α) s f =
      triangleLiftedHom c (K.map α.op s) f := by
  apply (SSet.uliftFunctor.{v, u}).map_injective
  rw [triangleLiftedHom_map, triangleLiftedHom_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate_naturality]

/-- 持ち上げた Hom 族の単体での評価は、元の小さい Hom 単体の同じ座標評価。 -/
lemma triangleLiftedHom_at_simplex {A H : SSet.{u}} {K : SSet.{max u v}} {n : ℕ}
    (c : A ⟶ (Δ[n] : SSet.{u})) (s : K _⦋n⦌)
    (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj H) :
    triangleLiftedHom c s f = c ≫ SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋n⦌) s).down := by
  apply (SSet.uliftFunctor.{v, u}).map_injective
  rw [triangleLiftedHom_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedCoordinate, Functor.map_comp]
  simp only [Category.assoc]
  erw [SSet.yonedaEquiv_symm_comp]
  erw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap (f.app (Opposite.op ⦋n⦌) s).down,
    Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
