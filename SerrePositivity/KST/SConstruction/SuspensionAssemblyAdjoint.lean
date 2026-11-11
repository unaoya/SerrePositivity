module
public import SerrePositivity.KST.SConstruction.SuspensionAssemblyNaturality

/-! # suspension の組み立ての随伴射
概要：反復間の suspension の射の随伴を loop 対象への自然な射として構成する。
方針：L9 の suspension–loop 随伴の Hom 同値と両変数の自然性を使う。
規約：随伴射の同値性・Ω 条件はここでは主張しない。使われ方：delooping の実装対象。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 概要：一次方向の境界商から次の反復の境界商の loop への随伴射。
方針：L9 の Hom 同値を構造射へ適用する。
規約：Kan 性や同値性の追加仮定なし。使われ方：Ω 条件の対象となる具体的な射。 -/
def oneDirectionAssemblyAdjoint (r : ℕ) (X : StableModel.{u}) :
    oneDirectionReducedRealization r X ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (boundaryReducedRealization (r + 1) X) :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (oneDirectionReducedRealization r X)
    (boundaryReducedRealization (r + 1) X)) (oneDirectionSuspensionAssembly r X)

/-- 概要：随伴射は安定な入力の射について自然。
方針：suspension の自然性へ Hom 同値を適用して両変数の自然性で移す。
規約：厳密な点つき射の等号。使われ方：Ω 条件の関手的な記述。 -/
lemma oneDirectionAssemblyAdjoint_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionReducedRealizationMap r f ≫ oneDirectionAssemblyAdjoint r Y =
      oneDirectionAssemblyAdjoint r X ≫
        (PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).map
          (boundaryReducedRealizationMap (r + 1) f) := by
  let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
  have h := congrArg (adj.homEquiv (oneDirectionReducedRealization r X)
      (boundaryReducedRealization (r + 1) Y)) (oneDirectionSuspensionAssembly_naturality r f)
  change adj.homEquiv _ _ ((PointedObject.smashFunctor.obj PointedSimplicialSet.circle.{u}).map
      (oneDirectionReducedRealizationMap r f) ≫ oneDirectionSuspensionAssembly r Y) =
    adj.homEquiv _ _ (oneDirectionSuspensionAssembly r X ≫
      boundaryReducedRealizationMap (r + 1) f) at h
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right] at h
  exact h

/-- 概要：反復の組み立ての随伴を自然変換にまとめる。
方針：各成分を既存の随伴射とする。
規約：源の S₁ 比較は別の自然変換。使われ方：反復間の Ω 比較の図式。 -/
def oneDirectionAssemblyAdjointNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⟶ boundaryReducedRealizationFunctor (r + 1) ⋙
      PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u} where
  app := oneDirectionAssemblyAdjoint r
  naturality {_X _Y} f := oneDirectionAssemblyAdjoint_naturality r f

/-- 概要：随伴射を戻すと元の suspension の組み立てを回収する。
方針：Hom 同値の逆合成の式。
規約：厳密等号。使われ方：Ω 条件と suspension の構造射の照合。 -/
lemma oneDirectionAssemblyAdjoint_uncurry (r : ℕ) (X : StableModel.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (oneDirectionReducedRealization r X)
    (boundaryReducedRealization (r + 1) X)).symm (oneDirectionAssemblyAdjoint r X) =
      oneDirectionSuspensionAssembly r X :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (oneDirectionReducedRealization r X)
    (boundaryReducedRealization (r + 1) X)).symm_apply_apply _

end SerrePositivity.KST.SConstruction
