module

public import SerrePositivity.InfinityCategories.Core.FixedDiagramHomotopy
public import SerrePositivity.InfinityCategories.Core.FatJoinCylinderExtension
public import SerrePositivity.InfinityCategories.Core.LaxSliceNaturality
public import SerrePositivity.InfinityCategories.Core.FatJoinCylinderFixedDiagram

/-!
概要：固定図式上の fatJoin の関手の同型から slice の関手の同型へ戻す。
方針：相対ホモトピーを fatJoin の円柱へ延長して slice へ curry する。
規約：slice の定義は既存の直接定義。
使われ方：Kerodon Lemma 4.6.4.25 の同型の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：slice への関手を固定図式上の fatJoin の関手の頂点で表す。
方針：slice の uncurry の固定条件を関手頂点へ移す。
規約：パラメーター A は任意。
使われ方：Kerodon Lemma 4.6.4.25 の比較する同型の端点。 -/
noncomputable def laxSliceFixedDiagramVertex {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ laxSlice p) :
    (vertexFiber ((pre (fatJoinInr A K)).app X) (functorVertex p)) _⦋0⦌ :=
  ⟨functorVertex (laxSliceUncurry f), by
    change functorVertex (fatJoinInr A K ≫ laxSliceUncurry f) =
      PinchedHom.constant (functorVertex p) 0
    rw [laxSliceUncurry_fixed, pinchedConstant_zero]⟩

/-- 概要：固定図式上で同型な fatJoin の二つの関手は、slice への関手として同型。
方針：固定図式上の可逆ホモトピーを左因子の可逆円柱へ延長し、slice へ curry する。
規約：X は quasicategory、A と K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の slice の同型の反映。 -/
lemma nonempty_functorIso_of_laxSliceFixedDiagramVertexIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (f g : A ⟶ laxSlice p)
    (e : VertexIso (X := vertexFiber ((pre (fatJoinInr A K)).app X) (functorVertex p))
      (laxSliceFixedDiagramVertex f) (laxSliceFixedDiagramVertex g)) :
    Nonempty (FunctorIso f g) := by
  obtain ⟨H, hH, hI⟩ := exists_relative_homotopy_of_fixedDiagram_vertexIso
    (fatJoinInr A K) p (laxSliceUncurry f) (laxSliceUncurry g)
    (laxSliceUncurry_fixed f) (laxSliceUncurry_fixed g) e
  have hH' : (fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K Δ[1] ≫ fatJoinInr A K ≫ laxSliceUncurry f := by
    rw [laxSliceUncurry_fixed]
    exact hH
  obtain ⟨F, h₀, h₁⟩ := exists_fatJoinCylinder_extension_of_relative_homotopy A K X
    (laxSliceUncurry f) (laxSliceUncurry g)
    (by rw [laxSliceUncurry_fixed, laxSliceUncurry_fixed]) H hH' hI
  have hF : fatJoinInr (A ⊗ equivalenceInterval) K ≫ F = p := by
    have he := congrArg (fun z ↦ fatJoinInr A K ≫ z) h₀
    simpa only [← Category.assoc, fatJoinInr_map, Category.id_comp,
      laxSliceUncurry_fixed] using he
  let G := laxSliceCurry F hF
  apply nonempty_functorIso_of_equivalenceCylinder_extension G
  · apply laxSliceUncurry_injective
    rw [laxSliceUncurry_precomp, laxSliceUncurry_curry]
    exact h₀
  · apply laxSliceUncurry_injective
    rw [laxSliceUncurry_precomp, laxSliceUncurry_curry]
    exact h₁

/-- 概要：slice の二つの同型な関手は、固定図式上の fatJoin の関手として同型。
方針：slice 内の可逆円柱を uncurry し、fatJoin の円柱の固定図式上の同型を使う。
規約：X は quasicategory、A と K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の同型の保存。 -/
lemma nonempty_laxSliceFixedDiagramVertexIso_of_functorIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {f g : A ⟶ laxSlice p} (e : FunctorIso f g) :
    Nonempty (VertexIso (X := vertexFiber ((pre (fatJoinInr A K)).app X) (functorVertex p))
      (laxSliceFixedDiagramVertex f) (laxSliceFixedDiagramVertex g)) := by
  obtain ⟨G, h₀, h₁⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  let F := laxSliceUncurry G
  have hF := laxSliceUncurry_fixed G
  have hf : fatJoinMap (equivalenceCylinderEndpoint A false) (𝟙 K) ≫ F = laxSliceUncurry f := by
    rw [← laxSliceUncurry_precomp, h₀]
  have hg : fatJoinMap (equivalenceCylinderEndpoint A true) (𝟙 K) ≫ F = laxSliceUncurry g := by
    rw [← laxSliceUncurry_precomp, h₁]
  obtain ⟨et⟩ := nonempty_fixedDiagramVertexIso_of_fatJoinCylinder A K X p F hF
  have hv₀ : fixedDiagramVertex (fatJoinInr A K) p
      (fatJoinMap (equivalenceCylinderEndpoint A false) (𝟙 K) ≫ F)
      (by rw [← Category.assoc, fatJoinInr_map, Category.id_comp, hF]) =
        laxSliceFixedDiagramVertex f := by
    apply Subtype.ext
    change functorVertex _ = functorVertex _
    rw [hf]
  have hv₁ : fixedDiagramVertex (fatJoinInr A K) p
      (fatJoinMap (equivalenceCylinderEndpoint A true) (𝟙 K) ≫ F)
      (by rw [← Category.assoc, fatJoinInr_map, Category.id_comp, hF]) =
        laxSliceFixedDiagramVertex g := by
    apply Subtype.ext
    change functorVertex _ = functorVertex _
    rw [hg]
  exact ⟨(eqToIso (congrArg SSet.HomotopyCategory.mk hv₀)).symm ≪≫ et ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk hv₁)⟩

/-- 概要：slice への二つの関手の同型の存在は、固定図式上の fatJoin の関手の同型の存在と同値。
方針：可逆円柱への延長と固定図式上の同型による二方向を組み合わせる。
規約：X は quasicategory、パラメーター A と添字 K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の正確な相対的同型判定。 -/
lemma nonempty_functorIso_iff_laxSliceFixedDiagramVertexIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (f g : A ⟶ laxSlice p) :
    Nonempty (FunctorIso f g) ↔
      Nonempty (VertexIso (X := vertexFiber ((pre (fatJoinInr A K)).app X) (functorVertex p))
        (laxSliceFixedDiagramVertex f) (laxSliceFixedDiagramVertex g)) := by
  constructor
  · rintro ⟨e⟩
    exact nonempty_laxSliceFixedDiagramVertexIso_of_functorIso e
  · rintro ⟨e⟩
    exact nonempty_functorIso_of_laxSliceFixedDiagramVertexIso f g e

end SerrePositivity.InfinityCategories
