module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftIntervalFatHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointLifting

/-!
概要：区間模型への任意の族の左 coslice fiber 模型によるホモトピーまでの回収。
方針：族を fat join に展開し、両端固定の join 図式への持ち上げを curry する。
規約：ここでは左模型の比較のホモトピー切断を示し、左逆の構成は別に要する。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、左 coslice fiber 模型と区間模型の比較の同値性の一方。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間模型への族は左 coslice fiber 模型への族の像としてホモトピーまで回収できる。
方針：両端固定の fat join 比較から図式と相対ホモトピーを取り、両方を族へ戻す。
規約：パラメータ A は任意、標的 X は quasicategory。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、比較射のホモトピー右逆の構成。 -/
lemma cosliceFiberToIntervalMappingSpace_exists_homotopy {A X : SSet.{u}}
    [Quasicategory X] {x y : X _⦋0⦌} (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    ∃ b : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y,
      Nonempty (SSet.Homotopy (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace x y) a) := by
  obtain ⟨G, hG, H, hH, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_joinDiagram_of_fatJoinDiagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalFatDiagram a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalFatDiagram a) rfl
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] A ≫ G = SSet.yonedaEquiv.symm x := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    have hh := congrArg
      (fun (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram (Δ[0] : SSet.{u}) A).obj d ⟶ X.obj d) ↦ q (Sum.inl z))
      (NatTrans.congr_app hG d)
    exact hh.trans (ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalFatDiagram_inl a) d) z)
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] A ≫ G = SSet.const y := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    have hh := congrArg
      (fun (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram (Δ[0] : SSet.{u}) A).obj d ⟶ X.obj d) ↦ q (Sum.inr z))
      (NatTrans.congr_app hG d)
    exact hh.trans (ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalFatDiagram_inr a) d) z)
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberCurry G hx hy
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry b = G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_curry G hx hy
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalCylinderSection A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] A ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison Δ[0] A ≫ G) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace x y) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace_uncurry, hb]
    simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_comparison]
    rfl
  have hxl : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm x := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨z, t⟩
    have hh := congrArg
      (fun (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram (Δ[0] : SSet.{u}) A ⊗ Δ[1]).obj d ⟶ X.obj d) ↦
        q (Sum.inl z, t)) (NatTrans.congr_app hH d)
    exact hh.trans (ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalFatDiagram_inl a) d) z)
  have hyl : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst A Δ[1] ≫ SSet.const y := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨z, t⟩
    have hh := congrArg
      (fun (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram (Δ[0] : SSet.{u}) A ⊗ Δ[1]).obj d ⟶ X.obj d) ↦
        q (Sum.inr z, t)) (NatTrans.congr_app hH d)
    exact hh.trans (ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalFatDiagram_inr a) d) z)
  exact ⟨b, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingHomotopyOfLeftFatJoin H (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace x y) a
    hF (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalFatDiagram_recover a) hxl hyl⟩⟩

/-- 概要：左模型の区間比較による後合成は任意のパラメータで本質的全射。
方針：回収した族のホモトピーを Kan な区間模型内の関手の同型に直す。
規約：指定された比較射そのものによる後合成を扱う。
使われ方：Kerodon §4.6.6（Tag 04HY）、左模型の比較の同値性の本質的全射の側。 -/
lemma cosliceFiberToIntervalMappingSpace_postcomp_essentiallySurjective {A X : SSet.{u}}
    [Quasicategory X] {x y : X _⦋0⦌} (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    ∃ b : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace x y) a) := by
  obtain ⟨b, ⟨H⟩⟩ := cosliceFiberToIntervalMappingSpace_exists_homotopy a
  exact ⟨b, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H⟩⟩

/-- 概要：左模型から区間模型への比較射はホモトピー切断を持つ。
方針：恒等族に任意パラメータの回収を適用する。
規約：左逆との合成のホモトピーは別の構成として区別する。
使われ方：Kerodon §4.6.6（Tag 04HY）、比較射のホモトピー逆の一方。 -/
lemma cosliceFiberToIntervalMappingSpace_exists_homotopy_section {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y,
      Nonempty (SSet.Homotopy (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace x y) (𝟙 _)) :=
  cosliceFiberToIntervalMappingSpace_exists_homotopy (𝟙 _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
