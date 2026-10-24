module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaFunctorSquare
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaArrowFamilies

/-!
概要：単位から出る comma の正方形の標的は、標準単位比較の下で右辺の族にホモトピック。
方針：関手正方形の合成関係の左辺を指定単位と認識し、区間族の Hom 表示で検出する。
規約：各点の単位比較の同値性は仮定しない。
使われ方：comma の写像空間から標準単位比較の導来 fiber への射の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単位を始点とする正方形の標的図式を Y の写像空間の族にする。
方針：零側辺の標的を F(x)、一側辺の標的を w の標的に揃えて curry する。
規約：正方形の標的図式を変更しない。
使われ方：単位比較の導来 fiber の始域側の座標。 -/
noncomputable def unitCommaSquareTargetFamily {A X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    A ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (unitCommaFiberTargetVertex G x w) :=
  intervalFamilyCurry s.target
    (s.target_zero.trans (unitCommaSectionVertex_target_const η x))
    (s.target_one.trans (unitCommaFiberTarget_const w))

/-- 概要：正規化した標的族の展開は元の正方形の標的図式。
方針：区間の curry の両逆。
規約：厳密な射の等式。
使われ方：正方形の上辺との照合。 -/
lemma unitCommaSquareTargetFamily_uncurry {A X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    intervalMappingUncurry (unitCommaSquareTargetFamily η x w s) = s.target :=
  intervalFamilyUncurry_curry _ _ _

/-- 概要：標的族の標準単位比較の像は正方形の右辺の族に実際にホモトピック。
方針：h Fun の合成関係と、前合成射・指定単位成分の認識を合わせる。
規約：単位の普遍性やパラメータの quasicategory 性を追加仮定しない。
使われ方：導来 fiber に値を持つ比較射の path 座標を与える。 -/
lemma unitCommaSquareTargetFamily_unit_homotopy {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    Nonempty (SSet.Homotopy
      (unitCommaSquareTargetFamily η x w s ≫
        unitIntervalMap η x (unitCommaFiberTargetVertex G x w))
      (unitCommaArrowFamily G x w A)) := by
  let a := unitCommaSquareTargetFamily η x w s
  let t := intervalFamilyHomotopy
    (a ≫ intervalFunctorMap G (F.app (Opposite.op ⦋0⦌) x) (unitCommaFiberTargetVertex G x w))
  have ht : SSet.ι₁ ≫ s.functorSquare = curry t.h := by
    rw [s.functorSquare_top]
    apply congrArg curry
    change (β_ A (Δ[1] : SSet.{u})).hom ≫ s.target ≫ G =
      (β_ A (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry
        (a ≫ intervalFunctorMap G _ _)
    rw [intervalFunctorMap_uncurry, unitCommaSquareTargetFamily_uncurry]
  have h := functorHom_comp_eq_of_square
    (unitCommaSectionVertexHomotopy (A := A) η x) (unitCommaVertexHomotopy G x w A)
    t s.functorSquare s.functorSquare_bottom ht s.functorSquare_left s.functorSquare_right
  rw [unitCommaSectionVertexHomotopy_hom] at h
  have hr : SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (unitCommaVertexHomotopy G x w A)) =
        intervalFamilyHom (unitCommaArrowFamily G x w A) := by
    change _ = SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (intervalFamilyHomotopy (unitCommaArrowFamily G x w A)))
    rw [unitCommaArrowFamily_homotopy]
  apply intervalFamilyHom_eq_imp_homotopy
  rw [unitIntervalMap, ← Category.assoc, intervalPrecompose_family]
  exact h.trans hr

end SerrePositivity.InfinityCategories
