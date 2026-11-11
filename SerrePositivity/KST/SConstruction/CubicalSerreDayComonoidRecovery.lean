module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayComonoidMonoidal

/-! # 元の Serre 余モノイド値 Day 関手の構造射の回収
概要：余モノイド値の構造射の underlying 鎖射と、元の比較の保存則を回収する。
方針：同じ鎖同型から作った構造の定義と、余モノイド射の二法則を使う。
規約：元の Serre 対角と増大を保持。使われ方：cubical rigidification と Λ の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の余モノイド同型の順射は同じ Day 鎖比較。 -/
lemma cubicalSerreDayComonoidIso_hom (K L : CubicalSet.{u}) :
    (cubicalSerreDayComonoidIso A K L).hom.hom = cubicalSerreDayComparison A K L := rfl

/-- 元の余モノイド同型の逆射は同じ Day 鎖組み立て。 -/
lemma cubicalSerreDayComonoidIso_inv (K L : CubicalSet.{u}) :
    (cubicalSerreDayComonoidIso A K L).inv.hom = cubicalSerreDayInverse A K L := rfl

/-- 元の余モノイド値 tensorator の鎖射は同じ全体の組み立て。 -/
lemma cubicalDaySerreComonoids_tensorator (X Y : CubicalDaySet.{u}) :
    (Functor.LaxMonoidal.μ (cubicalDaySerreComonoids A) X Y).hom =
      cubicalSerreDayInverse A X.functor Y.functor := rfl

/-- 元の余モノイド値 cotensorator の鎖射は同じ全体の Day 比較。 -/
lemma cubicalDaySerreComonoids_cotensorator (X Y : CubicalDaySet.{u}) :
    (Functor.OplaxMonoidal.δ (cubicalDaySerreComonoids A) X Y).hom =
      cubicalSerreDayComparison A X.functor Y.functor := rfl

/-- 元の余モノイド値単位射の鎖射は同じ単位生成 cell。 -/
lemma cubicalDaySerreComonoids_unit :
    (Functor.LaxMonoidal.ε (cubicalDaySerreComonoids A)).hom =
      cubicalSerreCell A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) cubicalDayUnitCell := rfl

/-- 元の余モノイド値逆単位射の鎖射は同じ Serre 増大。 -/
lemma cubicalDaySerreComonoids_counit :
    (Functor.OplaxMonoidal.η (cubicalDaySerreComonoids A)).hom =
      cubicalSerreAugmentation A cubicalDayUnit :=
  cubicalSerreDayComonoidUnit_inv A

/-- 元の Day 鎖比較は、元の両鎖複体の増大の tensor を保存する。 -/
lemma cubicalSerreDayComparison_counit (K L : CubicalSet.{u}) :
    cubicalSerreDayComparison A K L ≫
        (cubicalSerreAugmentation A K ⊗ₘ cubicalSerreAugmentation A L) ≫
          (λ_ (𝟙_ (Complex A))).hom =
      cubicalSerreAugmentation A (cubicalDayTensor K L) := by
  have h := IsComonHom.hom_counit (cubicalSerreDayComparison A K L)
  rw [Comon.tensorObj_counit] at h
  exact h

/-- 元の Day 鎖比較は、因子順を保つ Serre tensor 対角を保存する。 -/
lemma cubicalSerreDayComparison_comul (K L : CubicalSet.{u}) :
    cubicalSerreDayComparison A K L ≫
        (cubicalSerreDiagonal A K ⊗ₘ cubicalSerreDiagonal A L) ≫
          tensorμ ((cubicalSerreChains A).obj K) ((cubicalSerreChains A).obj K)
            ((cubicalSerreChains A).obj L) ((cubicalSerreChains A).obj L) =
      cubicalSerreDiagonal A (cubicalDayTensor K L) ≫
        (cubicalSerreDayComparison A K L ⊗ₘ cubicalSerreDayComparison A K L) := by
  have h := IsComonHom.hom_comul (cubicalSerreDayComparison A K L)
  rw [Comon.tensorObj_comul] at h
  exact h

end SerrePositivity.KST.SConstruction
