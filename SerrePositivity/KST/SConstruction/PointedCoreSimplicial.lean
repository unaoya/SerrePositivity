module
public import SerrePositivity.KST.SConstruction.CoreSimplicial
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-! # 零図式を基点とする単体的 core
概要：各段の零図式と面・退化写像を点つき単体集合の関手として束ねる。
方針：core の零頂点の厳密な自然性を Under 圏の可換条件に移す。
規約：BGT §7。全次数で同じ零頂点の選択を使う。
使われ方：対角実現と反復 S• の基点の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零図式を基点とする S_n C の core。
方針：選んだ零頂点を core の頂点として指定する。
規約：全次数で同じ零対象を使う。使われ方：単体的な点つき core。 -/
def pointedCoreSConstruction (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    PointedSimplicialSet.{u} :=
  PointedSimplicialSet.ofVertex (coreSConstruction n C)
    (coreSConstructionZeroVertex n (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).vertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).isZero)

/-- 概要：零図式を基点とする各段の core は Kan 複体。
方針：基点を忘れると元の core であることを使う。
規約：零対象を持つ quasicategory。使われ方：点つき Kan 列の各段。 -/
instance pointedCoreSConstruction_kanComplex (n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] : KanComplex (pointedCoreSConstruction n C).right :=
  coreSConstruction_kanComplex n C

/-- 概要：S• の単体作用は零図式の基点を厳密に保つ。
方針：零次の頂点の自然性を終対象からの基点射の等号へ移す。
規約：反変の向き。使われ方：点つき単体的 core の面・退化作用。 -/
def pointedCoreSMap {m n : ℕ} (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    pointedCoreSConstruction n C ⟶ pointedCoreSConstruction m C :=
  Under.homMk (coreSMap C θ) (by
    apply (SSet.unitHomEquiv _).injective
    change (coreSMap C θ).app (Opposite.op ⦋0⦌)
      (SSet.unitHomEquiv _ ((SSet.unitHomEquiv _).symm
        (coreSConstructionZeroVertex n (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).vertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).isZero))) =
      SSet.unitHomEquiv _ ((SSet.unitHomEquiv _).symm
        (coreSConstructionZeroVertex m (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).vertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).isZero))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact coreSMap_zeroVertex θ _ _)

/-- 概要：零図式の基点を持つ単体的 Kan core。
方針：各段の点つき core と基点を保つ単体作用を束ねる。
規約：各段は Kan、対角の Kan 性は別に置換する。
使われ方：K 空間の実現の基点と反復 S• の整合性。 -/
def simplicialPointedCoreSConstruction (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    SimplexCategoryᵒᵖ ⥤ PointedSimplicialSet.{u} where
  obj n := pointedCoreSConstruction n.unop.len C
  map θ := pointedCoreSMap C θ.unop.toOrderHom
  map_id n := by
    apply Under.UnderMorphism.ext
    exact (simplicialCoreSConstruction C).map_id n
  map_comp θ φ := by
    apply Under.UnderMorphism.ext
    exact (simplicialCoreSConstruction C).map_comp θ φ

/-- 概要：基点を忘れると元の単体的 Kan core と厳密に一致する。
方針：Under の射の基礎射を計算する。
規約：単体的対象の等号。使われ方：点つき構成と元の ιS•C の照合。 -/
lemma simplicialPointedCoreSConstruction_forget (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    simplicialPointedCoreSConstruction C ⋙ PointedSimplicialSet.forget =
      simplicialCoreSConstruction C := rfl

end SerrePositivity.KST.SConstruction
