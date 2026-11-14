module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Path
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-!
概要：二単体の全長 Hom の path 圏を標準区間へ厳密に同定する。
方針：唯一の内部点 1 の有無を二つの区間頂点へ送る。
規約：包含方向を保ち、全 path は終点 1 に送る。
使われ方：Ind-S (9) の全長 Hom 族の固定合成端。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 二単体の長い Hom の native な path 型。 -/
abbrev TriangleNativePath := Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)

/-- 合成端を表す全 path。 -/
def triangleFullPath : TriangleNativePath.{u} where
  I := Set.univ
  left_le := fun _ _ => Fin.zero_le _
  le_right := fun _ _ => Fin.le_last _

/-- 区間頂点が表す、内部点を含むか否かの path。 -/
def trianglePathFromInterval (j : ULift.{u} (Fin 2)) : TriangleNativePath.{u} where
  I := {k | k.down = 0 ∨ k.down = 2 ∨ j.down = 1}
  left := Or.inl rfl
  right := Or.inr (Or.inl rfl)
  left_le := fun _ _ => Fin.zero_le _
  le_right := fun _ _ => Fin.le_last _

/-- native path から、内部点の有無を表す区間頂点を読む。 -/
def trianglePathToInterval (p : TriangleNativePath.{u}) : ULift.{u} (Fin 2) := by
  classical
  exact ULift.up (if ULift.up (1 : Fin 3) ∈ p.I then 1 else 0)

lemma trianglePathFromInterval_toInterval (p : TriangleNativePath.{u}) :
    trianglePathFromInterval (trianglePathToInterval p) = p := by
  classical
  apply SimplicialThickening.Path.ext
  ext ⟨k⟩
  fin_cases k
  · simp [trianglePathFromInterval, p.left]
  · simp [trianglePathFromInterval, trianglePathToInterval]
  · simp [trianglePathFromInterval, p.right]

lemma trianglePathToInterval_fromInterval (j : ULift.{u} (Fin 2)) :
    trianglePathToInterval (trianglePathFromInterval j) = j := by
  classical
  rcases j with ⟨j⟩
  fin_cases j <;> simp [trianglePathToInterval, trianglePathFromInterval]

/-- 包含を保つ native path から区間への関手。 -/
def trianglePathIntervalFunctor : TriangleNativePath.{u} ⥤ ULift.{u} (Fin 2) where
  obj := trianglePathToInterval
  map {p q} f := homOfLE (by
    classical
    change (if ULift.up (1 : Fin 3) ∈ p.I then (1 : Fin 2) else 0) ≤
      (if ULift.up (1 : Fin 3) ∈ q.I then 1 else 0)
    split_ifs with hp hq
    · exact le_rfl
    · exact False.elim (hq (f.1.1.1 hp))
    · exact Fin.zero_le _
    · exact le_rfl)

/-- 区間から native path への包含方向の逆関手。 -/
def triangleIntervalPathFunctor : ULift.{u} (Fin 2) ⥤ TriangleNativePath.{u} where
  obj := trianglePathFromInterval
  map {p q} f := ⟨⟨⟨by
    intro k hk
    rcases hk with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by have := f.le; change p.down ≤ q.down at this; omega))⟩⟩⟩

/-- native 全長 Hom の path nerve は標準区間そのもの。 -/
def triangleNativePathIntervalIso : nerve TriangleNativePath.{u} ≅ (Δ[1] : SSet.{u}) :=
  (show nerve TriangleNativePath.{u} ≅ nerve (ULift.{u} (Fin 2)) from
    { hom := nerveMap trianglePathIntervalFunctor
      inv := nerveMap triangleIntervalPathFunctor
      hom_inv_id := by
        change nerveMap (trianglePathIntervalFunctor ⋙ triangleIntervalPathFunctor) = nerveMap (𝟭 _)
        congr 1
        exact CategoryTheory.Functor.ext (fun p => trianglePathFromInterval_toInterval p)
      inv_hom_id := by
        change nerveMap (triangleIntervalPathFunctor ⋙ trianglePathIntervalFunctor) = nerveMap (𝟭 _)
        congr 1
        exact CategoryTheory.Functor.ext (fun j => trianglePathToInterval_fromInterval j) }) ≪≫
    (stdSimplex.isoNerve 1).symm

/-- 宇宙を上げた同じ全長 path も大きい宇宙の標準区間と同型。 -/
def uliftTriangleNativePathIntervalIso :
    (SSet.uliftFunctor.{v, u}).obj (nerve TriangleNativePath.{u}) ≅
      (Δ[1] : SSet.{max u v}) :=
  (SSet.uliftFunctor.{v, u}).mapIso triangleNativePathIntervalIso ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso 1

/-- 標準区間の終点は元の全 path を厳密に回収する。 -/
lemma triangleNativePathIntervalIso_inv_last :
    triangleNativePathIntervalIso.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = ComposableArrows.mk₀ triangleFullPath.{u} := by
  apply CategoryTheory.Functor.ext (fun i => ?_)
  change trianglePathFromInterval (ULift.up (1 : Fin 2)) = triangleFullPath
  apply SimplicialThickening.Path.ext
  ext k
  simp [trianglePathFromInterval, triangleFullPath]

/-- 宇宙を上げても、標準終点は同じ全 path を回収する。 -/
lemma uliftTriangleNativePathIntervalIso_inv_last :
    uliftTriangleNativePathIntervalIso.{u, v}.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        ULift.up (ComposableArrows.mk₀ triangleFullPath.{u}) := by
  change ULift.up (triangleNativePathIntervalIso.inv.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
  rw [triangleNativePathIntervalIso_inv_last]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
