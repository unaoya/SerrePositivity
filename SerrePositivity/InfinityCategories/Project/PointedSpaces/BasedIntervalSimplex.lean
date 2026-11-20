module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SquareConstantCorners
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyInvariance

/-!
概要：両端が同じ基点である区間写像と、その両端固定ホモトピーを境界定数単体へ移す。
方針：一次境界の二つの頂点を計算し、境界の単体を二つの面へ因子分解する。
規約：元の区間族を保持。使われ方：円評価の Hom 経路の基本群の類の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.BasedInterval
end SerrePositivity.KST.Spectra.BasedInterval
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.BasedInterval
variable {Y : SSet.{u}} {x : Y _⦋0⦌}

/-- 両端を同じ基点に写す元の区間写像を、そのまま境界定数一単体にする。 -/
def simplex (f : (Δ[1] : SSet.{u}) ⟶ Y)
    (h : ∀ i : Fin 2, f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) = x) :
    Y.PtSimplex 1 x where
  map := f
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, SSet.comp_const]
    fin_cases j
    · erw [stdSimplex.δ_zero_eq_const.{u}, SSet.const_comp, h]
    · erw [stdSimplex.δ_one_eq_const.{u}, SSet.const_comp, h]

/-- 両端固定の区間ホモトピーは、二つの頂点面上で同じ基点に定値。 -/
lemma homotopy_face {f g : (Δ[1] : SSet.{u}) ⟶ Y} (H : SSet.Homotopy f g)
    (hs : lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      H.h = SSet.const x)
    (ht : lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      H.h = SSet.const x) (j : Fin 2) :
    stdSimplex.δ j ▷ (Δ[1] : SSet.{u}) ≫ H.h = SSet.const x := by
  have hf (i : Fin 2) :
      (SSet.const (X := (Δ[0] : SSet.{u})) (stdSimplex.obj₀Equiv.symm i)) ▷ Δ[1] =
        snd (Δ[0] : SSet.{u}) Δ[1] ≫
          lift (SSet.const (stdSimplex.obj₀Equiv.symm i)) (𝟙 (Δ[1] : SSet.{u})) := by
    rfl
  fin_cases j
  · erw [stdSimplex.δ_zero_eq_const.{u}, hf, Category.assoc, ht, SSet.comp_const]
  · erw [stdSimplex.δ_one_eq_const.{u}, hf, Category.assoc, hs, SSet.comp_const]

/-- 同じ元の区間族を使って、両端固定ホモトピーを境界固定単体のホモトピーにする。 -/
def relativeHomotopy {f g : (Δ[1] : SSet.{u}) ⟶ Y}
    (hf : ∀ i : Fin 2, f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) = x)
    (hg : ∀ i : Fin 2, g.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) = x)
    (H : SSet.Homotopy f g)
    (hs : lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      H.h = SSet.const x)
    (ht : lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      H.h = SSet.const x) : (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.simplex f hf).Homotopy (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.simplex g hg) where
  h := H.h
  h₀ := H.h₀
  h₁ := H.h₁
  rel := by
    simp only [Subcomplex.ofSimplex_ι, SSet.comp_const]
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨s, hs'⟩, t⟩
    simp only [boundary_eq_iSup, stdSimplex.face_singleton_compl, Subfunctor.iSup_obj,
      Set.mem_iUnion, Subcomplex.mem_ofSimplex_obj_iff] at hs'
    obtain ⟨j, ⟨v, rfl⟩⟩ := hs'
    exact congrArg (fun k : (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ Y ↦
      k.app (Opposite.op ⦋d⦌) (stdSimplex.objEquiv.{u}.symm v, t))
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.homotopy_face H hs ht j)

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
