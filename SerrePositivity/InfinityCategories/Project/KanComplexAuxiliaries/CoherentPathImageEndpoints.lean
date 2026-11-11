module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentStringPathFlags

/-! # 元の Path の像と端点の移送の照合
概要：端点の表示だけを替えた像関手を、元の thickening の像関手と照合する。
方針：同じ像集合を持つ Path を作り、端点の等式の消去で元の作用を回収する。
規約：Path の集合や全包含を変更せず、端点の等式だけを移す。
使われ方：精密化の Path 単体を、元の coherent 図式の同じ豊穣作用で評価する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open scoped _root_.Simplicial

/-- 元の Path の像を、指定した同じ端点の表示で取る関手。 -/
def coherentPathImageFunctor {J K : Type u} [LinearOrder J] [LinearOrder K]
    (θ : J →o K) {a b : J} {c d : K} (ha : θ a = c) (hb : θ b = d) :
    Path a b ⥤ Path c d where
  obj p :=
    { I := θ '' p.I
      left := ⟨a, p.left, ha⟩
      right := ⟨b, p.right, hb⟩
      left_le x hx := by
        rcases hx with ⟨z, hz, rfl⟩
        rw [← ha]
        exact θ.monotone (p.left_le z hz)
      le_right x hx := by
        rcases hx with ⟨z, hz, rfl⟩
        rw [← hb]
        exact θ.monotone (p.le_right z hz) }
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- 端点の表示だけを移した像の nerve は、元の豊穣再添字の Hom 作用と同じ。 -/
lemma coherentPathImageFunctor_nerve_heq {J K : Type u} [LinearOrder J] [LinearOrder K]
    (θ : J →o K) {a b : J} {c d : K} (ha : θ a = c) (hb : θ b = d) :
    HEq (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor θ ha hb))
      ((SimplicialThickening.functor θ).map (.mk a) (.mk b)) := by
  cases ha
  cases hb
  rfl

/-- 合成列の精密化による元の Path の像も、同じ native な豊穣再添字である。 -/
lemma coherentStringPathReindexFunctor_native_heq {I : Type u} [SmallCategory I]
    {x y : I} {f : x ⟶ y} {s t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f} (a : s ⟶ t) :
    HEq (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathReindexFunctor a))
      ((SimplicialThickening.functor a.map.toOrderHom.uliftMap).map
        (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last s.length)))) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor_nerve_heq a.map.toOrderHom.uliftMap
    (congrArg ULift.up a.first) (congrArg ULift.up a.last)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentPathImageFunctor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentPathImageFunctor_nerve_heq := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor_nerve_heq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentStringPathReindexFunctor_native_heq := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathReindexFunctor_native_heq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentPathImageFunctor._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentPathImageFunctor._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentPathImageFunctor._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentPathImageFunctor._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentPathImageFunctor._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentPathImageFunctor._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentPathImageFunctor._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentPathImageFunctor._proof_7
