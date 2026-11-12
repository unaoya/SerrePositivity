module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Path

/-!
# Path の Hom 単体集合の内部点座標

概要：path と内部点の部分集合の対応を単体集合の同型へ上げる。
方針：包含を保存する互いに逆の関手の nerve を使う。
規約：Mathlib の包含順序を固定する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM） の立方体を構成する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.SimplicialThickening

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：内部点への制限を path の圏から包含順序の圏への関手にする。
方針：path の射が持つ包含を開区間へ制限する。
規約：Mathlib の包含方向。
使われ方：Kerodon 2.4.5.4（Tag 00LM） の立方体座標。 -/
def pathInteriorFunctor : Path a b ⥤ Set (Set.Ioo a b) where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInterior
  map f := homOfLE (fun _ hx ↦ f.1.1.1 hx)
/-- 概要：内部点の部分集合から path を作る操作は関手になる。
方針：端点以外の点に与えられた包含を適用する。
規約：a<b。
使われ方：Kerodon 2.4.5.4（Tag 00LM） の立方体座標の逆。 -/
def pathOfInteriorFunctor (hab : a < b) : Set (Set.Ioo a b) ⥤ Path a b where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hab
  map {S T} f := by
    refine ⟨⟨⟨?_⟩⟩⟩
    intro x hx
    rcases hx with rfl | rfl | ⟨hx, hS⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨hx, f.le hS⟩)
/-- 概要：内部点への制限と端点付加の合成は恒等関手。
方針：対象上の逆写像性と薄い射を用いる。
規約：関手の厳密な等式。
使われ方：Kerodon 2.4.5.4（Tag 00LM） の Hom 同型の逆合成。 -/
lemma pathInteriorFunctor_comp_pathOfInteriorFunctor (hab : a < b) :
    pathInteriorFunctor ⋙ pathOfInteriorFunctor hab = 𝟭 (Path a b) := by
  apply CategoryTheory.Functor.ext (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior_pathInterior hab p)
/-- 概要：端点付加と内部点への制限の合成は恒等関手。
方針：内部点上の逆写像性と薄い射を用いる。
規約：関手の厳密な等式。
使われ方：Kerodon 2.4.5.4（Tag 00LM） の Hom 同型の逆合成。 -/
lemma pathOfInteriorFunctor_comp_pathInteriorFunctor (hab : a < b) :
    pathOfInteriorFunctor hab ⋙ pathInteriorFunctor = 𝟭 (Set (Set.Ioo a b)) := by
  apply CategoryTheory.Functor.ext (fun S ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInterior_pathOfInterior hab S)

/-- 概要：path の Hom 単体集合は内部点の冪集合の nerve と同型。
方針：互いに厳密な逆の関手の nerve を取る。
規約：包含座標を用い、補集合は取らない。
使われ方：Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の立方体への帰着。 -/
def pathInteriorNerveIso (hab : a < b) : nerve (Path a b) ≅ nerve (Set (Set.Ioo a b)) where
  hom := nerveMap pathInteriorFunctor
  inv := nerveMap (pathOfInteriorFunctor hab)
  hom_inv_id := by
    change nerveMap (pathInteriorFunctor ⋙ pathOfInteriorFunctor hab) = nerveMap (𝟭 _)
    rw [pathInteriorFunctor_comp_pathOfInteriorFunctor hab]
  inv_hom_id := by
    change nerveMap (pathOfInteriorFunctor hab ⋙ pathInteriorFunctor) = nerveMap (𝟭 _)
    rw [pathOfInteriorFunctor_comp_pathInteriorFunctor hab]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
