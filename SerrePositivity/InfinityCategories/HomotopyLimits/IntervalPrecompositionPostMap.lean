module

public import SerrePositivity.InfinityCategories.F1B.IntervalComposition
public import SerrePositivity.InfinityCategories.F1B.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostIso

/-!
概要：元の区間 Hom 前合成は、単体的関手の元の Hom 作用と全パラメータで両立する。
方針：元の h Fun の作用と定値関手の輸送の可換式を使う。
規約：端点を正規化しても元の前合成と指定辺の一単体を保持する。
使われ方：Yoneda 評価の自然性を P_Σ の元の包含作用へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の前合成と単体的関手の元の区間 Hom 作用は、一つの関手同型で可換。 -/
def intervalFunctorMap_precomposeIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y)
    {a b : X _⦋0⦌} (e : SSet.Edge a b) (z : X _⦋0⦌) :
    FunctorIso
      (intervalPrecompose z (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        intervalFunctorMap p a z)
      (intervalFunctorMap p b z ≫ intervalPrecompose (p.app (Opposite.op ⦋0⦌) z)
        (SSet.Truncated.HomotopyCategory.homMk (e.map p).toTruncated)) := by
  apply functorIsoOfSimplicialHomotopy
  apply Classical.choice
  apply intervalFamilyHom_eq_imp_homotopy
  let K := intervalMappingSpace b z
  let γ := SSet.Truncated.HomotopyCategory.homMk e.toTruncated
  have hconst := constantFunctorHomMap_postcomp K p γ
  have hc := congrArg (fun t ↦ t ≫ (constantFunctorCompIso K b p).inv) hconst
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc
  rw [intervalFunctorMap_familyHom, intervalPrecompose_hom, Functor.map_comp,
    intervalPrecompose_family]
  have hm := intervalFunctorMap_familyHom (𝟙 (intervalMappingSpace b z)) p
  simp only [Category.id_comp] at hm
  rw [hm]
  have h := congrArg (fun t ↦ t ≫
    (hoFunctor.map ((ihom K).map p)).toFunctor.map (intervalFamilyHom (𝟙 K)) ≫
      (constantFunctorCompIso K z p).hom) hc
  simp only [Category.assoc] at h ⊢
  exact h

/-- 端点の表示を変えない正規化 Hom 作用は、元の区間関手作用と厳密に一致する。 -/
lemma intervalMappingPostOfEq_refl_eq_functorMap {X Y : SSet.{u}} (p : X ⟶ Y)
    (a b : X _⦋0⦌) :
    intervalMappingPostOfEq p a b rfl rfl = intervalFunctorMap p a b := by
  apply intervalMappingUncurry_injective
  have h := intervalMappingPostOfEq_uncurry p a b rfl rfl (𝟙 _)
  have h' := intervalFunctorMap_uncurry (𝟙 (intervalMappingSpace a b)) p
  simp only [Category.id_comp] at h h'
  exact h.trans h'.symm

/-- 端点表示を正規化しても、元の前合成と同じ指定辺の Hom 作用は全族で可換。 -/
def intervalMappingPostOfEq_precomposeIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y)
    {a b : X _⦋0⦌} (e : SSet.Edge a b) (z : X _⦋0⦌) {a' b' z' : Y _⦋0⦌}
    (ha : p.app (Opposite.op ⦋0⦌) a = a') (hb : p.app (Opposite.op ⦋0⦌) b = b')
    (hz : p.app (Opposite.op ⦋0⦌) z = z') (e' : SSet.Edge a' b')
    (he : p.app (Opposite.op ⦋1⦌) e.edge = e'.edge) :
    FunctorIso
      (intervalPrecompose z (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        intervalMappingPostOfEq p a z ha hz)
      (intervalMappingPostOfEq p b z hb hz ≫
        intervalPrecompose z' (SSet.Truncated.HomotopyCategory.homMk e'.toTruncated)) := by
  subst a' b' z'
  have he' : e.map p = e' := SSet.Edge.ext he
  subst e'
  rw [intervalMappingPostOfEq_refl_eq_functorMap, intervalMappingPostOfEq_refl_eq_functorMap]
  exact intervalFunctorMap_precomposeIso p e z

end SerrePositivity.InfinityCategories.HomotopyLimits
