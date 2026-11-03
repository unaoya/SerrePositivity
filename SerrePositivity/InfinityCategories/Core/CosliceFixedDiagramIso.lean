module
public import SerrePositivity.InfinityCategories.Core.Coslice
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinder
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderFunctorIso
public import SerrePositivity.InfinityCategories.Core.FatJoin
public import SerrePositivity.InfinityCategories.Core.FatJoinFunctor
public import SerrePositivity.InfinityCategories.Core.FixedDiagramCylinderIso
public import SerrePositivity.InfinityCategories.Core.FixedDiagramHomotopy
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinLifting
public import SerrePositivity.InfinityCategories.Core.JoinTensor
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.PinchedHom.Basic
public import SerrePositivity.InfinityCategories.Core.CoconeFixedComparison
public import SerrePositivity.InfinityCategories.Core.CosliceCylinderExtension
public import SerrePositivity.InfinityCategories.Core.CosliceCylinderFixedDiagram
public import SerrePositivity.InfinityCategories.Core.LaxCoslice
public import SerrePositivity.InfinityCategories.Core.LaxCosliceNaturality
public import SerrePositivity.InfinityCategories.Core.LaxCosliceUncurry
public import SerrePositivity.InfinityCategories.Core.LaxCosliceUniversal

/-! # Coslice の族と固定左図式上の同型

概要：coslice への族の同型は、固定左図式上の余錐の関手の同型と同値。
方針：相対ホモトピーを右因子の可逆円柱へ延長して curry する。
規約：通常の coslice と太い coslice の両方を扱う。使われ方：比較同値の反映。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coslice への族を固定左図式上の関手圏の頂点にする。
方針：uncurry の固定条件を関手頂点へ移す。
規約：パラメーターは任意。使われ方：族の同型判定。 -/
def sliceUnderFixedDiagramVertex {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceUnder p) :
    (vertexFiber ((pre (joinInl K A)).app X) (functorVertex p)) _⦋0⦌ :=
  ⟨functorVertex (sliceUnderUncurry f), by
    change functorVertex (joinInl K A ≫ sliceUnderUncurry f) =
      PinchedHom.constant (functorVertex p) 0
    rw [sliceUnderUncurry_fixed, pinchedConstant_zero]⟩

/-- 概要：固定図式上で同型な join の二つの関手は、slice への関手として同型。
方針：固定図式上の可逆ホモトピーを左因子の可逆円柱へ延長し、slice へ curry する。
規約：X は quasicategory、A と K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の slice の同型の反映。 -/
lemma nonempty_functorIso_of_sliceUnderFixedDiagramVertexIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (f g : A ⟶ sliceUnder p)
    (e : VertexIso (X := vertexFiber ((pre (joinInl K A)).app X) (functorVertex p))
      (sliceUnderFixedDiagramVertex f) (sliceUnderFixedDiagramVertex g)) :
    Nonempty (FunctorIso f g) := by
  obtain ⟨H, hH, hI⟩ := exists_relative_homotopy_of_fixedDiagram_vertexIso
    (joinInl K A) p (sliceUnderUncurry f) (sliceUnderUncurry g)
    (sliceUnderUncurry_fixed f) (sliceUnderUncurry_fixed g) e
  have hH' : (joinInl K A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K Δ[1] ≫ joinInl K A ≫ sliceUnderUncurry f := by
    rw [sliceUnderUncurry_fixed]
    exact hH
  obtain ⟨F, h₀, h₁⟩ := exists_joinRightCylinder_extension_of_relative_homotopy A K X
    (sliceUnderUncurry f) (sliceUnderUncurry g)
    (by rw [sliceUnderUncurry_fixed, sliceUnderUncurry_fixed]) H hH' hI
  have hF : joinInl K (A ⊗ equivalenceInterval) ≫ F = p := by
    have he := congrArg (fun z ↦ joinInl K A ≫ z) h₀
    simpa only [← Category.assoc, joinInl_joinMap, Category.id_comp,
      sliceUnderUncurry_fixed] using he
  let G := sliceUnderCurry F hF
  apply nonempty_functorIso_of_equivalenceCylinder_extension G
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact h₀
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact h₁

/-- 概要：slice の二つの同型な関手は、固定図式上の join の関手として同型。
方針：slice 内の可逆円柱を uncurry し、join の円柱の固定図式上の同型を使う。
規約：X は quasicategory、A と K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の同型の保存。 -/
lemma nonempty_sliceUnderFixedDiagramVertexIso_of_functorIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {f g : A ⟶ sliceUnder p} (e : FunctorIso f g) :
    Nonempty (VertexIso (X := vertexFiber ((pre (joinInl K A)).app X) (functorVertex p))
      (sliceUnderFixedDiagramVertex f) (sliceUnderFixedDiagramVertex g)) := by
  obtain ⟨G, h₀, h₁⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  let F := sliceUnderUncurry G
  have hF := sliceUnderUncurry_fixed G
  have hf : joinMap (𝟙 K) (equivalenceCylinderEndpoint A false) ≫ F = sliceUnderUncurry f := by
    rw [← sliceUnderUncurry_precomp, h₀]
  have hg : joinMap (𝟙 K) (equivalenceCylinderEndpoint A true) ≫ F = sliceUnderUncurry g := by
    rw [← sliceUnderUncurry_precomp, h₁]
  obtain ⟨et⟩ := nonempty_fixedDiagramVertexIso_of_joinRightCylinder A K X p F hF
  have hv₀ : fixedDiagramVertex (joinInl K A) p
      (joinMap (𝟙 K) (equivalenceCylinderEndpoint A false) ≫ F)
      (by rw [← Category.assoc, joinInl_joinMap, Category.id_comp, hF]) =
        sliceUnderFixedDiagramVertex f := by
    apply Subtype.ext
    change functorVertex _ = functorVertex _
    rw [hf]
  have hv₁ : fixedDiagramVertex (joinInl K A) p
      (joinMap (𝟙 K) (equivalenceCylinderEndpoint A true) ≫ F)
      (by rw [← Category.assoc, joinInl_joinMap, Category.id_comp, hF]) =
        sliceUnderFixedDiagramVertex g := by
    apply Subtype.ext
    change functorVertex _ = functorVertex _
    rw [hg]
  exact ⟨(eqToIso (congrArg SSet.HomotopyCategory.mk hv₀)).symm ≪≫ et ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk hv₁)⟩

/-- 概要：slice への二つの関手の同型の存在は、固定図式上の join の関手の同型の存在と同値。
方針：可逆円柱への延長と固定図式上の同型による二方向を組み合わせる。
規約：X は quasicategory、パラメーター A と添字 K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の正確な相対的同型判定。 -/
lemma nonempty_functorIso_iff_sliceUnderFixedDiagramVertexIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (f g : A ⟶ sliceUnder p) :
    Nonempty (FunctorIso f g) ↔
      Nonempty (VertexIso (X := vertexFiber ((pre (joinInl K A)).app X) (functorVertex p))
        (sliceUnderFixedDiagramVertex f) (sliceUnderFixedDiagramVertex g)) := by
  constructor
  · rintro ⟨e⟩
    exact nonempty_sliceUnderFixedDiagramVertexIso_of_functorIso e
  · rintro ⟨e⟩
    exact nonempty_functorIso_of_sliceUnderFixedDiagramVertexIso f g e


/-- 概要：coslice への族を固定左図式上の関手圏の頂点にする。
方針：uncurry の固定条件を関手頂点へ移す。
規約：パラメーターは任意。使われ方：族の同型判定。 -/
noncomputable def laxCosliceFixedDiagramVertex {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ laxCoslice p) :
    (vertexFiber ((pre (fatJoinInl K A)).app X) (functorVertex p)) _⦋0⦌ :=
  ⟨functorVertex (laxCosliceUncurry f), by
    change functorVertex (fatJoinInl K A ≫ laxCosliceUncurry f) =
      PinchedHom.constant (functorVertex p) 0
    rw [laxCosliceUncurry_fixed, pinchedConstant_zero]⟩

/-- 概要：固定図式上で同型な fatJoin の二つの関手は、slice への関手として同型。
方針：固定図式上の可逆ホモトピーを左因子の可逆円柱へ延長し、slice へ curry する。
規約：X は quasicategory、A と K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の slice の同型の反映。 -/
lemma nonempty_functorIso_of_laxCosliceFixedDiagramVertexIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (f g : A ⟶ laxCoslice p)
    (e : VertexIso (X := vertexFiber ((pre (fatJoinInl K A)).app X) (functorVertex p))
      (laxCosliceFixedDiagramVertex f) (laxCosliceFixedDiagramVertex g)) :
    Nonempty (FunctorIso f g) := by
  obtain ⟨H, hH, hI⟩ := exists_relative_homotopy_of_fixedDiagram_vertexIso
    (fatJoinInl K A) p (laxCosliceUncurry f) (laxCosliceUncurry g)
    (laxCosliceUncurry_fixed f) (laxCosliceUncurry_fixed g) e
  have hH' : (fatJoinInl K A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K Δ[1] ≫ fatJoinInl K A ≫ laxCosliceUncurry f := by
    rw [laxCosliceUncurry_fixed]
    exact hH
  obtain ⟨F, h₀, h₁⟩ := exists_fatJoinRightCylinder_extension_of_relative_homotopy A K X
    (laxCosliceUncurry f) (laxCosliceUncurry g)
    (by rw [laxCosliceUncurry_fixed, laxCosliceUncurry_fixed]) H hH' hI
  have hF : fatJoinInl K (A ⊗ equivalenceInterval) ≫ F = p := by
    have he := congrArg (fun z ↦ fatJoinInl K A ≫ z) h₀
    simpa only [← Category.assoc, fatJoinInl_map, Category.id_comp,
      laxCosliceUncurry_fixed] using he
  let G := laxCosliceCurry F hF
  apply nonempty_functorIso_of_equivalenceCylinder_extension G
  · apply laxCosliceUncurry_injective
    rw [laxCosliceUncurry_precomp, laxCosliceUncurry_curry]
    exact h₀
  · apply laxCosliceUncurry_injective
    rw [laxCosliceUncurry_precomp, laxCosliceUncurry_curry]
    exact h₁

/-- 概要：slice の二つの同型な関手は、固定図式上の fatJoin の関手として同型。
方針：slice 内の可逆円柱を uncurry し、fatJoin の円柱の固定図式上の同型を使う。
規約：X は quasicategory、A と K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の同型の保存。 -/
lemma nonempty_laxCosliceFixedDiagramVertexIso_of_functorIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {f g : A ⟶ laxCoslice p} (e : FunctorIso f g) :
    Nonempty (VertexIso (X := vertexFiber ((pre (fatJoinInl K A)).app X) (functorVertex p))
      (laxCosliceFixedDiagramVertex f) (laxCosliceFixedDiagramVertex g)) := by
  obtain ⟨G, h₀, h₁⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  let F := laxCosliceUncurry G
  have hF := laxCosliceUncurry_fixed G
  have hf : fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A false) ≫ F = laxCosliceUncurry f := by
    rw [← laxCosliceUncurry_precomp, h₀]
  have hg : fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A true) ≫ F = laxCosliceUncurry g := by
    rw [← laxCosliceUncurry_precomp, h₁]
  obtain ⟨et⟩ := nonempty_fixedDiagramVertexIso_of_fatJoinRightCylinder A K X p F hF
  have hv₀ : fixedDiagramVertex (fatJoinInl K A) p
      (fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A false) ≫ F)
      (by rw [← Category.assoc, fatJoinInl_map, Category.id_comp, hF]) =
        laxCosliceFixedDiagramVertex f := by
    apply Subtype.ext
    change functorVertex _ = functorVertex _
    rw [hf]
  have hv₁ : fixedDiagramVertex (fatJoinInl K A) p
      (fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A true) ≫ F)
      (by rw [← Category.assoc, fatJoinInl_map, Category.id_comp, hF]) =
        laxCosliceFixedDiagramVertex g := by
    apply Subtype.ext
    change functorVertex _ = functorVertex _
    rw [hg]
  exact ⟨(eqToIso (congrArg SSet.HomotopyCategory.mk hv₀)).symm ≪≫ et ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk hv₁)⟩

/-- 概要：slice への二つの関手の同型の存在は、固定図式上の fatJoin の関手の同型の存在と同値。
方針：可逆円柱への延長と固定図式上の同型による二方向を組み合わせる。
規約：X は quasicategory、パラメーター A と添字 K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の正確な相対的同型判定。 -/
lemma nonempty_functorIso_iff_laxCosliceFixedDiagramVertexIso
    {A K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (f g : A ⟶ laxCoslice p) :
    Nonempty (FunctorIso f g) ↔
      Nonempty (VertexIso (X := vertexFiber ((pre (fatJoinInl K A)).app X) (functorVertex p))
        (laxCosliceFixedDiagramVertex f) (laxCosliceFixedDiagramVertex g)) := by
  constructor
  · rintro ⟨e⟩
    exact nonempty_laxCosliceFixedDiagramVertexIso_of_functorIso e
  · rintro ⟨e⟩
    exact nonempty_functorIso_of_laxCosliceFixedDiagramVertexIso f g e


end SerrePositivity.InfinityCategories
