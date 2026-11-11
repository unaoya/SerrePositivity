module
public import SerrePositivity.KST.SConstruction.TracedCompositePointTraces
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeDataTransport

/-! # 元の全木を保つ合成補正の一点制限と全区間の展開
概要：元の合成補正の全円柱・全合成木を一点へ制限し、前後二本の全 trace へ展開する。
方針：保存済みの同じ全証人を前合成し、元の二部分の厳密な制限式を合成する。
規約：合成木を選び直さず、元の全二単体・全区間・順序を保持する。
使われ方：実 BF 段三角形の合成辺を、三入力の左右の全辺路へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories Spectra.PointedMapping
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の全合成補正円柱と全木の同じ直通列制限。 -/
def monicKPrismCompositePointData (n : ℕ) :=
  (monicKPrismNativeCompositeCorrectionData F f g n).precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g))

/-- 元の同じ全円柱を、同じ指定直通列点へ制限した写像を厳密に保持する。 -/
lemma monicKPrismCompositePointData_h (n : ℕ) :
    (monicKPrismCompositePointData F f g n).homotopy.h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeCompositeCorrectionData F f g n).homotopy.h := rfl

/-- 合成木の全三角形は、元の同じ全二単体の直通列制限を同じ順序で保持する。 -/
lemma monicKPrismCompositePointData_triangles (n : ℕ) :
    familyChainCompositionTriangles (monicKPrismCompositePointData F f g n).witness =
      (familyChainCompositionTriangles
        (monicKPrismNativeCompositeCorrectionData F f g n).witness).map
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[2] : SSet.{u})) ≫ ·) :=
  FamilyChainCompositeData.precomp_triangles _ _

/-- 元の合成木に記録した全区間は、元の前後二本の補正全区間の像の順序付き連結。 -/
lemma monicKPrismCompositePointData_trace (n : ℕ) :
    familyChainCompositionInputTrace (monicKPrismCompositePointData F f g n).witness =
      monicKPrismCompositePointFirstTrace F f g n ++
        monicKPrismCompositePointSecondTrace F f g n := by
  change familyChainCompositionInputTrace (familyChainWitnessPrecomp _ _) = _
  rw [familyChainWitnessPrecomp_trace, monicKPrismNativeCompositeCorrectionData_trace,
    monicKPrismTracedCompositeCorrectionChain_trace]
  simp only [List.map_append, List.map_map, Function.comp_def]
  exact congrArg₂ (· ++ ·) (monicKPrismCompositeFirstTrace_point F f g n)
    (monicKPrismCompositeSecondTrace_point F f g n)

/-- 零段の元の全補正列には区間を追加しない。 -/
lemma monicKPrismCompositePointData_zero_trace :
    familyChainCompositionInputTrace (monicKPrismCompositePointData F f g 0).witness = [] := by
  rw [monicKPrismCompositePointData_trace]
  rfl

/-- 零段の元の同じ全円柱は、元の合成射の定数写像そのもの。 -/
lemma monicKPrismCompositePointData_zero :
    (monicKPrismCompositePointData F f g 0).homotopy.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫
        SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) := by
  rw [monicKPrismCompositePointData_h, monicKPrismNativeCompositeCorrectionData_zero,
    whiskerRight_fst_assoc, SSet.comp_const]

end SerrePositivity.KST.SConstruction
