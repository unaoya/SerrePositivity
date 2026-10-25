module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ColimitCoconeCompletion
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
public import SerrePositivity.InfinityCategories.Stable.UniverseHorns

/-!
概要：全四角形族の頂点を読み戻し、同じ引き戻し錐・押し出し余錐へ制限する。
方針：前合成と関手頂点の全単射の往復、ホーン形状の同型を使う。
規約：元の四角形の全単体を保持する。宇宙持ち上げは形状だけに明示する。
使われ方：Ind の点ごとの filtered 補完に有限交換と余極限同士の交換を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 関手頂点の元の実四角形。 -/
def functorVertexSquare {X : SSet.{u}}
    (v : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X := (functorVertexEquiv _ _).symm v

/-- 元の実四角形の読み戻しは、全空間の後合成と交換する。 -/
lemma functorVertexSquare_postcompose {X Y : SSet.{u}}
    (v : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌) (F : X ⟶ Y) :
    functorVertexSquare (((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map F).app
      (Opposite.op ⦋0⦌) v) = functorVertexSquare v ≫ F := by
  obtain ⟨f, rfl⟩ := (functorVertexEquiv _ _).surjective v
  rfl

/-- 小さい cospan の持ち上げた錐と、大きい宇宙の元の正方形の実同型。 -/
def uliftCospanSquareReadingIso :
    join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (horn 2 2)) ≅
      (Δ[1] : SSet.{max u v}) ⊗ Δ[1] :=
  joinIso (Iso.refl Δ[0]) (uliftHornIso.{u, v} 2 2) ≪≫ cospanConeSquareIso

/-- 小さい cospan の持ち上げた錐を、大きい宇宙の実四角形へ同定する。 -/
def uliftCospanSquareReading :
    join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (horn 2 2)) ⟶
      (Δ[1] : SSet.{max u v}) ⊗ Δ[1] :=
  joinMap (𝟙 Δ[0]) (uliftHornIso.{u, v} 2 2).hom ≫ cospanConeSquareIso.hom

/-- 持ち上げた cospan への読み戻しの極限性は、元の実四角形の引き戻し性。 -/
lemma functorVertexSquare_pullback_iff {X : SSet.{max u v}}
    (v : ((ihom ((Δ[1] : SSet.{max u v}) ⊗ Δ[1])).obj X) _⦋0⦌) :
    IsLimitCone (functorVertexCone
      (((pre uliftCospanSquareReading.{u, v}).app X).app (Opposite.op ⦋0⦌) v)) ↔
      IsPullbackSquare (functorVertexSquare v) := by
  let c := pullbackCone (functorVertexSquare v)
  have he : (functorVertexCone
      (((pre uliftCospanSquareReading.{u, v}).app X).app (Opposite.op ⦋0⦌) v)).val =
      (restrictJoinCone c (uliftHornIso.{u, v} 2 2).hom).val := by
    change (functorVertexEquiv _ _).symm _ = _
    rw [functorVertexMap_precomp]
    exact Category.assoc _ _ _
  exact (isLimitCone_iff_of_cone_val_eq _ _ he).trans
    (isLimitCone_restrict_iff_of_isIso c (uliftHornIso.{u, v} 2 2).hom)

/-- 元の span への読み戻しの余極限性は、同じ実四角形の押し出し性。 -/
lemma functorVertexSquare_pushout_iff {X : SSet.{u}}
    (v : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌) :
    IsColimitCone (functorVertexCocone
      (((pre spanCoconeSquareIso.hom).app X).app (Opposite.op ⦋0⦌) v)) ↔
      IsPushoutSquare (functorVertexSquare v) := by
  apply isColimitCone_iff_of_coconeMap_eq
  exact functorVertexMap_precomp _ v

end SerrePositivity.InfinityCategories.F2
