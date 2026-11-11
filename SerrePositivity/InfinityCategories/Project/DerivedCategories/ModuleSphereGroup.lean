module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ModuleSphereRelation
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # 正次数 π の線形商による表示

概要：単体的加群の正次数ホモトピー群を球面単体の Moore 境界による商として表す。
方針：充填関係の比較で商の全単射を作り、隣接退化の和で群の積を計算する。
規約：乗法群と加法群は Multiplicative を介して比較する。
使われ方：π と Moore ホモロジーの線形比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] (W : SimplicialObject (ModuleCat.{v} S))

/-- 概要：球面単体を Moore 境界で割った加群。
方針：零番目の面の像で商を取る。
規約：正次数 n+1。使われ方：Moore ホモロジーの具体的表示。 -/
abbrev sphereHomologyQuotient (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule W n ⧸ LinearMap.range (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphereBoundaryMap W n)

/-- 概要：境界零単体の和は Kan の積を表す。
方針：最後の二つの退化の和を三面の充填として取る。
規約：K-L9 の積と同じ最後の添字。使われ方：π の群演算と線形商の加法の比較。 -/
def moduleSphereAddMulStruct {n : ℕ}
    (f g : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).PtSimplex (n + 1) 0) :
    SSet.PtSimplex.MulStruct f g
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n f + _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n g)) (Fin.last n) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n f
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n g
  let i : Fin (n + 1) := Fin.last n
  let t := W.σ i.castSucc G.val + W.σ i.succ F.val
  refine { map := SSet.yonedaEquiv.symm t
           δ_castSucc_castSucc_map := ?_
           δ_succ_castSucc_map := ?_
           δ_succ_succ_map := ?_
           δ_map_of_lt := ?_
           δ_map_of_gt := ?_ }
  · apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    change W.δ i.castSucc.castSucc t = G.val
    dsimp only [t]
    rw [map_add, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face]
    simp [Fin.ext_iff, show i.val ≠ i.val + 1 + 1 by omega]
  · apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv_symm_value]
    change W.δ i.castSucc.succ t = F.val + G.val
    dsimp only [t]
    rw [map_add, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face]
    have hne₁ : i.val + 1 ≠ i.val := by omega
    have hne₂ : i.val + 1 ≠ i.val + 1 + 1 := by omega
    simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, hne₁, hne₂, ite_false, ite_true]
    exact add_comm _ _
  · apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    change W.δ i.succ.succ t = F.val
    dsimp only [t]
    rw [map_add, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face]
    simp [Fin.ext_iff, show i.val + 1 + 1 ≠ i.val by omega]
  · intro j hj
    change j < i.castSucc.castSucc at hj
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.module_yoneda_const_zero]
    change W.δ j t = 0
    dsimp only [t]
    rw [map_add, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face]
    have h₁ : j ≠ i.castSucc.castSucc := ne_of_lt hj
    have h₂ : j ≠ i.castSucc.succ := ne_of_lt (lt_trans hj (Fin.castSucc_lt_succ))
    have h₃ : j ≠ i.succ.castSucc := by
      simpa only [Fin.succ_castSucc] using h₂
    have h₄ : j ≠ i.succ.succ := ne_of_lt
      (lt_trans (lt_trans hj (show i.castSucc.castSucc < i.castSucc.succ from Fin.castSucc_lt_succ))
        (by simpa only [Fin.succ_castSucc] using
          (show i.succ.castSucc < i.succ.succ from Fin.castSucc_lt_succ)))
    simp only [h₁, h₂, h₃, h₄, ite_false, add_zero]
  · intro j hj
    have : j.val < n + 3 := j.is_lt
    simp only [Fin.lt_def, Fin.val_succ, Fin.val_last] at hj
    omega

/-- 概要：正次数ホモトピー群と球面単体の境界商の全単射。
方針：K-L9 の関係と Moore 境界の比較で Quotient.congr を適用する。
規約：Kan 性のみを追加仮定とする。使われ方：群同型の台。 -/
def modulePiSphereEquiv [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0 ≃ sphereHomologyQuotient W n :=
  Quotient.congr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n) (fun f g => by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel f g ↔ _
    rw [Submodule.quotientRel_def]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct 0).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleRelStruct_iff_boundary W f g))

/-- 概要：正次数 π の群演算は Moore 境界商の加法に一致する。
方針：二つの代表について明示した退化の和の積充填を使う。
規約：次数は n+1。使われ方：π と Moore ホモロジーの群同型。 -/
def modulePiSphereGroupEquiv [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0 ≃*
      Multiplicative (sphereHomologyQuotient W n) where
  __ := modulePiSphereEquiv W n
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h f =>
    induction b using Quotient.inductionOn with | h g =>
    change (modulePiSphereEquiv W n) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g) =
      (modulePiSphereEquiv W n) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f) +
        (modulePiSphereEquiv W n) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq (moduleSphereAddMulStruct W f g)]
    change Submodule.Quotient.mk
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n).symm _)) =
        Submodule.Quotient.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n f) +
          (Submodule.Quotient.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n g) : sphereHomologyQuotient W n)
    rw [Equiv.apply_symm_apply]
    rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
