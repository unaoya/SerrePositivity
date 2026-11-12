module

public import SerrePositivity.KST.Spectra.SkeletalFiberRepresentatives

/-!
概要：低い骨格で定数の射から境界定数単体を全ての正次数で取り出す。
方針：低い骨格への単体の持ち上げと、セル球面への相対商の評価を使う。
規約：次数一を含む。係数群の可換性は要求しない。
使われ方：Goerss–Jardine VIII §1。次数一の骨格 cochain の代表と fiber 係数。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalMapSimplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SkeletalCellAttachment UnbasedPointedMapping

variable (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (f : (K.skeleton (n + 2) : SSet.{u}) ⟶ Y.right)
    (hf : skeletalInclusion K n ≫ f = SSet.const Y.basepoint)

include hf in
/-- 低い骨格で定数の射は、その次元以下の単体上で定数。 -/
lemma lower_constant (s : (K.skeleton (n + 2) : SSet.{u}) _⦋n⦌) :
    SSet.yonedaEquiv.symm s ≫ f = SSet.const Y.basepoint := by
  let t : (K.skeleton (n + 1) : SSet.{u}) _⦋n⦌ := ⟨s.val, K.mem_skeleton _⟩
  have he : SSet.yonedaEquiv.symm t ≫ skeletalInclusion K n = SSet.yonedaEquiv.symm s := by
    rw [yonedaEquiv_symm_comp]
    rfl
  rw [← he, Category.assoc, hf, comp_const]

/-- 骨格の射による単体の像を境界定数単体として読む。 -/
def simplex (s : K _⦋n + 1⦌) : Y.right.PtSimplex (n + 1) Y.basepoint where
  map := SSet.yonedaEquiv.symm (⟨s, K.mem_skeleton _⟩ :
    (K.skeleton (n + 2) : SSet.{u}) _⦋n + 1⦌) ≫ f
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm, lower_constant K Y n f hf]

/-- 退化単体の像は代表そのものとして定数。 -/
lemma simplex_degeneracy (s : K _⦋n⦌) (i : Fin (n + 1)) :
    simplex K Y n f hf (K.σ i s) = .const := by
  apply RelativeMorphism.ext
  change SSet.yonedaEquiv.symm (⟨K.σ i s, K.mem_skeleton _⟩ :
    (K.skeleton (n + 2) : SSet.{u}) _⦋n + 1⦌) ≫ f = SSet.const Y.basepoint
  have he : (⟨K.σ i s, K.mem_skeleton _⟩ :
      (K.skeleton (n + 2) : SSet.{u}) _⦋n + 1⦌) =
      (K.skeleton (n + 2) : SSet.{u}).σ i ⟨s, K.mem_skeleton _⟩ := rfl
  rw [he, ← stdSimplex.σ_comp_yonedaEquiv_symm, Category.assoc,
    lower_constant K Y n f hf, comp_const]

/-- 元の骨格射の fiber 頂点は、同じセル単体からの復元と厳密に一致する。 -/
lemma fiberVertex_eq : skeletalFiberVertex K Y n f hf =
    stageFiberSimplexVertex K Y n (fun s ↦ simplex K Y n f hf s.val) := by
  let g := relativeMap K Y (n + 1) f hf
  have hr : ∀ c : relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1),
      cellRestriction K Y (n + 1) g c = (SimplexCell.sphereIso.{u} (n + 1)).hom ≫
        (SphereSimplex.equiv Y (n + 1)).symm (simplex K Y n f hf c.simplex) := by
    intro c
    apply (cancel_epi (SimplexCell.sphereIso.{u} (n + 1)).inv).1
    rw [Iso.inv_hom_id_assoc]
    apply (SphereSimplex.equiv Y (n + 1)).injective
    rw [Equiv.apply_symm_apply]
    apply RelativeMorphism.ext
    exact cellRestriction_simplex_map K Y (n + 1) f hf c
  change relativeFiberVertex K Y n g = _
  rw [← relativeFiberVertex_cellRestrictions]
  unfold stageFiberSimplexVertex
  congr 1
  funext s
  rw [hr]
  have hs : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s).simplex = s.val :=
    congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).apply_symm_apply s)
  rw [hs]

/-- 元の骨格射の成分係数は、同じ単体のホモトピー類。 -/
lemma fiberVertex_coefficient [KanComplex Y.right] (s : K.nonDegenerate (n + 1)) :
    stageFiberComponentEquiv K Y n (π₀.mk (skeletalFiberVertex K Y n f hf)) s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (simplex K Y n f hf s.val) := by
  rw [fiberVertex_eq, stageFiberComponentEquiv_simplexVertex]

end
end SerrePositivity.KST.Spectra.SkeletalMapSimplex
