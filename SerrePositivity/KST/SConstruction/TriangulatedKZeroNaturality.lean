module
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroMap
public import SerrePositivity.KST.SConstruction.ObjectKClassNaturality
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorTriangulated

/-! # 三角圏 K₀ と実際の BF 零次 K 群の比較の自然性
概要：順方向の比較準同型が完全関手の三角圏 K₀ への作用と BF K 群への作用を結ぶ。
方針：三角圏 K₀ の普遍性により元の対象類の自然性へ帰着する。
規約：比較の全単射性を仮定しない。使われ方：π₀ K 比較の自然同型への拡張。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open Spectra
open scoped Simplicial

/-- 本レーンの完全射の保存条件は安定圏レーンの完全性を与える。 -/
lemma stableModelHom_exact {X Y : StableModel.{u}} (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val :=
  ⟨f.property.1, f.property.2⟩

/-- 完全関手が三角圏の Grothendieck 群へ誘導する準同型。 -/
def triangulatedKZeroSourceMap {X Y : StableModel.{u}} (f : X ⟶ Y) :
    TriangulatedK0 (hoFunctor.obj X.carrier) →+ TriangulatedK0 (hoFunctor.obj Y.carrier) := by
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val := stableModelHom_exact f
  exact TriangulatedK0.map (hoFunctor.map f.val).toFunctor

/-- 三角圏 K₀ の誘導準同型は対象の類を像の対象の類へ送る。 -/
lemma triangulatedKZeroSourceMap_mk {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : hoFunctor.obj X.carrier) :
    triangulatedKZeroSourceMap f (TriangulatedK0.mk a) =
      TriangulatedK0.mk ((hoFunctor.map f.val).toFunctor.obj a) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val := stableModelHom_exact f
  exact TriangulatedK0.map_mk (hoFunctor.map f.val).toFunctor a

/-- 実際の零次 K 群の誘導準同型はホモトピー圏の対象 K 類を保つ。 -/
lemma homotopyObjectKClass_naturality {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : hoFunctor.obj X.carrier) :
    (kHomotopyMap f 0).toAdditive (homotopyObjectKClass X a) =
      homotopyObjectKClass Y ((hoFunctor.map f.val).toFunctor.obj a) := by
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  exact objectKClass_naturality f x

/-- 順方向の三角圏 K₀ 比較は元の完全関手の作用に関して自然。 -/
lemma triangulatedKZeroMap_naturality {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (triangulatedKZeroMap Y).comp (triangulatedKZeroSourceMap f) =
      (kHomotopyMap f 0).toAdditive.comp (triangulatedKZeroMap X) := by
  apply TriangulatedK0.hom_ext
  intro a
  simp only [AddMonoidHom.comp_apply, triangulatedKZeroSourceMap_mk, triangulatedKZeroMap_mk]
  exact (homotopyObjectKClass_naturality f a).symm

end SerrePositivity.KST.SConstruction
