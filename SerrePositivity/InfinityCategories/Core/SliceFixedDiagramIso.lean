module

public import SerrePositivity.InfinityCategories.Core.FixedDiagramHomotopy
public import SerrePositivity.InfinityCategories.Core.JoinCylinderExtension
public import SerrePositivity.InfinityCategories.Core.JoinTensor
public import SerrePositivity.InfinityCategories.Core.JoinCylinderFixedDiagram

/-!
概要：固定図式上の join の関手の同型から slice の関手の同型へ戻す。
方針：相対ホモトピーを join の円柱へ延長して slice へ curry する。
規約：slice の定義は既存の直接定義。
使われ方：Kerodon Lemma 4.6.4.25 の同型の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：slice への関手を固定図式上の join の関手の頂点で表す。
方針：slice の uncurry の固定条件を関手頂点へ移す。
規約：パラメーター A は任意。
使われ方：Kerodon Lemma 4.6.4.25 の比較する同型の端点。 -/
def sliceOverFixedDiagramVertex {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) :
    (vertexFiber ((pre (joinInr A K)).app X) (functorVertex p)) _⦋0⦌ :=
  ⟨functorVertex (sliceOverUncurry f), by
    change functorVertex (joinInr A K ≫ sliceOverUncurry f) =
      PinchedHom.constant (functorVertex p) 0
    rw [sliceOverUncurry_fixed, pinchedConstant_zero]⟩

/-- 概要：固定図式上で同型な join の二つの関手は、slice への関手として同型。
方針：固定図式上の可逆ホモトピーを左因子の可逆円柱へ延長し、slice へ curry する。
規約：X は quasicategory、A と K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の slice の同型の反映。 -/
lemma nonempty_functorIso_of_sliceOverFixedDiagramVertexIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (f g : A ⟶ sliceOver p)
    (e : VertexIso (X := vertexFiber ((pre (joinInr A K)).app X) (functorVertex p))
      (sliceOverFixedDiagramVertex f) (sliceOverFixedDiagramVertex g)) :
    Nonempty (FunctorIso f g) := by
  obtain ⟨H, hH, hI⟩ := exists_relative_homotopy_of_fixedDiagram_vertexIso
    (joinInr A K) p (sliceOverUncurry f) (sliceOverUncurry g)
    (sliceOverUncurry_fixed f) (sliceOverUncurry_fixed g) e
  have hH' : (joinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K Δ[1] ≫ joinInr A K ≫ sliceOverUncurry f := by
    rw [sliceOverUncurry_fixed]
    exact hH
  obtain ⟨F, h₀, h₁⟩ := exists_joinCylinder_extension_of_relative_homotopy A K X
    (sliceOverUncurry f) (sliceOverUncurry g)
    (by rw [sliceOverUncurry_fixed, sliceOverUncurry_fixed]) H hH' hI
  have hF : joinInr (A ⊗ equivalenceInterval) K ≫ F = p := by
    have he := congrArg (fun z ↦ joinInr A K ≫ z) h₀
    simpa only [← Category.assoc, joinInr_joinMap, Category.id_comp,
      sliceOverUncurry_fixed] using he
  let G := sliceOverCurry F hF
  apply nonempty_functorIso_of_equivalenceCylinder_extension G
  · apply sliceOverUncurry_injective
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    exact h₀
  · apply sliceOverUncurry_injective
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    exact h₁

/-- 概要：slice の二つの同型な関手は、固定図式上の join の関手として同型。
方針：slice 内の可逆円柱を uncurry し、join の円柱の固定図式上の同型を使う。
規約：X は quasicategory、A と K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の同型の保存。 -/
lemma nonempty_sliceOverFixedDiagramVertexIso_of_functorIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {f g : A ⟶ sliceOver p} (e : FunctorIso f g) :
    Nonempty (VertexIso (X := vertexFiber ((pre (joinInr A K)).app X) (functorVertex p))
      (sliceOverFixedDiagramVertex f) (sliceOverFixedDiagramVertex g)) := by
  obtain ⟨G, h₀, h₁⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  let F := sliceOverUncurry G
  have hF := sliceOverUncurry_fixed G
  have hf : joinMap (equivalenceCylinderEndpoint A false) (𝟙 K) ≫ F = sliceOverUncurry f := by
    rw [← sliceOverUncurry_precomp, h₀]
  have hg : joinMap (equivalenceCylinderEndpoint A true) (𝟙 K) ≫ F = sliceOverUncurry g := by
    rw [← sliceOverUncurry_precomp, h₁]
  obtain ⟨et⟩ := nonempty_fixedDiagramVertexIso_of_joinCylinder A K X p F hF
  have hv₀ : fixedDiagramVertex (joinInr A K) p
      (joinMap (equivalenceCylinderEndpoint A false) (𝟙 K) ≫ F)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp, hF]) =
        sliceOverFixedDiagramVertex f := by
    apply Subtype.ext
    change functorVertex _ = functorVertex _
    rw [hf]
  have hv₁ : fixedDiagramVertex (joinInr A K) p
      (joinMap (equivalenceCylinderEndpoint A true) (𝟙 K) ≫ F)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp, hF]) =
        sliceOverFixedDiagramVertex g := by
    apply Subtype.ext
    change functorVertex _ = functorVertex _
    rw [hg]
  exact ⟨(eqToIso (congrArg SSet.HomotopyCategory.mk hv₀)).symm ≪≫ et ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk hv₁)⟩

/-- 概要：slice への二つの関手の同型の存在は、固定図式上の join の関手の同型の存在と同値。
方針：可逆円柱への延長と固定図式上の同型による二方向を組み合わせる。
規約：X は quasicategory、パラメーター A と添字 K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の正確な相対的同型判定。 -/
lemma nonempty_functorIso_iff_sliceOverFixedDiagramVertexIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (f g : A ⟶ sliceOver p) :
    Nonempty (FunctorIso f g) ↔
      Nonempty (VertexIso (X := vertexFiber ((pre (joinInr A K)).app X) (functorVertex p))
        (sliceOverFixedDiagramVertex f) (sliceOverFixedDiagramVertex g)) := by
  constructor
  · rintro ⟨e⟩
    exact nonempty_sliceOverFixedDiagramVertexIso_of_functorIso e
  · rintro ⟨e⟩
    exact nonempty_functorIso_of_sliceOverFixedDiagramVertexIso f g e

end SerrePositivity.InfinityCategories
