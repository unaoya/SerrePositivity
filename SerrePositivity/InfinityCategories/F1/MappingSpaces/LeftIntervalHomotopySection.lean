module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.LeftIntervalFatHomotopy
public import SerrePositivity.InfinityCategories.F1.Joins.JoinEndpointLifting

/-!
概要：区間模型への任意の族の左 coslice fiber 模型によるホモトピーまでの回収。
方針：族を fat join に展開し、両端固定の join 図式への持ち上げを curry する。
規約：ここでは左模型の比較のホモトピー切断を示し、左逆の構成は別に要する。
使われ方：Kerodon §4.6.5–4.6.6、左 coslice fiber 模型と区間模型の比較の同値性の一方。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：区間模型への族は左 coslice fiber 模型への族の像としてホモトピーまで回収できる。
方針：両端固定の fat join 比較から図式と相対ホモトピーを取り、両方を族へ戻す。
規約：パラメータ A は任意、標的 X は quasicategory。
使われ方：Kerodon §4.6.5–4.6.6、比較射のホモトピー右逆の構成。 -/
lemma cosliceFiberToIntervalMappingSpace_exists_homotopy {A X : SSet.{u}}
    [Quasicategory X] {x y : X _⦋0⦌} (a : A ⟶ intervalMappingSpace x y) :
    ∃ b : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y,
      Nonempty (SSet.Homotopy (b ≫ cosliceFiberToIntervalMappingSpace x y) a) := by
  obtain ⟨G, hG, H, hH, _⟩ := exists_joinDiagram_of_fatJoinDiagram
    (fatJoinEndpointInclusion Δ[0] A ≫ leftIntervalFatDiagram a)
    (leftIntervalFatDiagram a) rfl
  have hx : joinInl Δ[0] A ≫ G = SSet.yonedaEquiv.symm x := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    have hh := congrArg
      (fun (q : (joinEndpointDiagram (Δ[0] : SSet.{u}) A).obj d ⟶ X.obj d) ↦ q (Sum.inl z))
      (NatTrans.congr_app hG d)
    exact hh.trans (ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (leftIntervalFatDiagram_inl a) d) z)
  have hy : joinInr Δ[0] A ≫ G = SSet.const y := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    have hh := congrArg
      (fun (q : (joinEndpointDiagram (Δ[0] : SSet.{u}) A).obj d ⟶ X.obj d) ↦ q (Sum.inr z))
      (NatTrans.congr_app hG d)
    exact hh.trans (ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (leftIntervalFatDiagram_inr a) d) z)
  let b := cosliceFiberCurry G hx hy
  have hb : cosliceFiberUncurry b = G := cosliceFiberUncurry_curry G hx hy
  have hF : leftIntervalCylinderSection A ≫ fatJoinCylinder Δ[0] A ≫
      (fatJoinComparison Δ[0] A ≫ G) =
      intervalMappingUncurry (b ≫ cosliceFiberToIntervalMappingSpace x y) := by
    rw [cosliceFiberToIntervalMappingSpace_uncurry, hb]
    simp only [← Category.assoc, fatJoinCylinder_comparison]
    rfl
  have hxl : (fatJoinInl Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm x := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨z, t⟩
    have hh := congrArg
      (fun (q : (joinEndpointDiagram (Δ[0] : SSet.{u}) A ⊗ Δ[1]).obj d ⟶ X.obj d) ↦
        q (Sum.inl z, t)) (NatTrans.congr_app hH d)
    exact hh.trans (ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (leftIntervalFatDiagram_inl a) d) z)
  have hyl : (fatJoinInr Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst A Δ[1] ≫ SSet.const y := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨z, t⟩
    have hh := congrArg
      (fun (q : (joinEndpointDiagram (Δ[0] : SSet.{u}) A ⊗ Δ[1]).obj d ⟶ X.obj d) ↦
        q (Sum.inr z, t)) (NatTrans.congr_app hH d)
    exact hh.trans (ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (leftIntervalFatDiagram_inr a) d) z)
  exact ⟨b, ⟨intervalMappingHomotopyOfLeftFatJoin H (b ≫ cosliceFiberToIntervalMappingSpace x y) a
    hF (leftIntervalFatDiagram_recover a) hxl hyl⟩⟩

/-- 概要：左模型の区間比較による後合成は任意のパラメータで本質的全射。
方針：回収した族のホモトピーを Kan な区間模型内の関手の同型に直す。
規約：指定された比較射そのものによる後合成を扱う。
使われ方：Kerodon §4.6.6、左模型の比較の同値性の本質的全射の側。 -/
lemma cosliceFiberToIntervalMappingSpace_postcomp_essentiallySurjective {A X : SSet.{u}}
    [Quasicategory X] {x y : X _⦋0⦌} (a : A ⟶ intervalMappingSpace x y) :
    ∃ b : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y, Nonempty (FunctorIso (b ≫ cosliceFiberToIntervalMappingSpace x y) a) := by
  obtain ⟨b, ⟨H⟩⟩ := cosliceFiberToIntervalMappingSpace_exists_homotopy a
  exact ⟨b, ⟨functorIsoOfSimplicialHomotopy H⟩⟩

/-- 概要：左模型から区間模型への比較射はホモトピー切断を持つ。
方針：恒等族に任意パラメータの回収を適用する。
規約：左逆との合成のホモトピーは別の構成として区別する。
使われ方：Kerodon §4.6.6、比較射のホモトピー逆の一方。 -/
lemma cosliceFiberToIntervalMappingSpace_exists_homotopy_section {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    ∃ r : intervalMappingSpace x y ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y,
      Nonempty (SSet.Homotopy (r ≫ cosliceFiberToIntervalMappingSpace x y) (𝟙 _)) :=
  cosliceFiberToIntervalMappingSpace_exists_homotopy (𝟙 _)

end SerrePositivity.InfinityCategories
