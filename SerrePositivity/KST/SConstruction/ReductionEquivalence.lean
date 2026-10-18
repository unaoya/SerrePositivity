module
public import SerrePositivity.KST.SConstruction.DiagonalReduction
public import SerrePositivity.KST.SConstruction.LocalizedTrivialFibrations
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanPushoutCube

/-! # 可縮な零段を潰す商写像の可逆性
概要：可縮 Kan な零段を一点へ潰す商写像は anodyne 局所化で可逆。
方針：同じ単射を持つ二つの pushout の cube を HA の定理で比較する。
規約：商の標的や対角の Kan 性を仮定しない。使われ方：自然な基点への模型の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：可縮 Kan 複体から終対象への射は trivial Kan fibration。
方針：全境界を充填し、終対象の一意性で基底との可換性を得る。
規約：終対象は cartesian tensor unit。使われ方：商の pushout cube の縦射。 -/
lemma trivialKanFibration_toUnit_of_contractible {A : SSet.{u}} (hA : IsContractibleKan A) :
    TrivialKanFibration (toUnit A) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  obtain ⟨F, hF⟩ := hA n a
  exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := isTerminalTensorUnit.hom_ext _ _ }

/-- 概要：可縮 Kan な部分を一点へ潰す商写像は anodyne を反転する全関手で可逆。
方針：元の標的を表す自明 pushout と商を表す pushout の cube を比較する。
規約：包含は単射、標的の Kan 性は不要。使われ方：零段を潰した実現との比較。 -/
lemma cofiberQuotient_image_isIso_of_contractible {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (hA : IsContractibleKan A) :
    IsIso (L.map (PointedObject.cofiberQuotient i)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hQ : anodyneExtensions.IsInvertedBy Q := Localization.inverts Q anodyneExtensions
  have ht := trivialKanFibration_toUnit_of_contractible hA
  have hc : IsIso (Q.map (toUnit A)) := map_isIso_of_trivialKanFibration Q hQ (toUnit A)
  have hidA : IsIso (Q.map (𝟙 A)) := by rw [Q.map_id]; infer_instance
  have hidB : IsIso (Q.map (𝟙 B)) := by rw [Q.map_id]; infer_instance
  have hs : IsPushout i (𝟙 A) (𝟙 B) i := IsPushout.of_vert_isIso ⟨by simp⟩
  have hs' : IsPushout i (toUnit A) (PointedObject.cofiberQuotient i) (PointedObject.cofiber i).hom :=
    IsPushout.of_hasPushout i (toUnit A)
  exact KanPushoutCube.image_isIso i (𝟙 A) (𝟙 B) i hs
    i (toUnit A) (PointedObject.cofiberQuotient i) (PointedObject.cofiber i).hom hs'
    (𝟙 A) (𝟙 B) (toUnit A) (PointedObject.cofiberQuotient i)
    (by simp) (by simp) (by simp) (PointedObject.cofiberQuotient_condition i)
    hidA hidB hc L hL

/-- 概要：可縮 Kan な零段を潰す対角の商写像は anodyne を反転する全関手で可逆。
方針：零段の包含の単射性と一般の cofiber 商写像の比較を使う。
規約：対角の Kan 性は不要。使われ方：従来の実現との自然な比較。 -/
lemma diagonalReductionQuotient_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (hX : IsContractibleKan (X.obj (Opposite.op ⦋0⦌))) :
    IsIso (L.map (diagonalReductionQuotient X)) :=
  cofiberQuotient_image_isIso_of_contractible L hL (diagonalZeroColumn X) hX

end SerrePositivity.KST.SConstruction
