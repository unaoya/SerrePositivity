module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.PointedModuleSimplex

/-! # 境界零単体の Moore 境界

概要：正規化された単体の零番目の面は球面単体であり、退化の面を明示する。
方針：面・退化の単体的恒等式を線形に評価する。
規約：球面単体の次数は n+1。使われ方：充填関係と Moore 境界の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] (W : SimplicialObject (ModuleCat.{v} S))

/-- 概要：球面単体の全ての面は零。
方針：核の共通部分の所属条件を取り出す。
規約：正次数。使われ方：退化の面の計算。 -/
lemma sphericalModule_face {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule W n) (j : Fin (n + 2)) :
    W.δ j s.val = 0 := (Submodule.mem_iInf _).1 s.property j

/-- 概要：正規化単体の正の面は零。
方針：具体的共通核の所属条件を取り出す。
規約：零番目の面を含めない。使われ方：Moore 境界の球面性。 -/
lemma mooreKernelModule_face {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelModule W (n + 1)) (j : Fin (n + 1)) :
    W.δ j.succ s.val = 0 := (Submodule.mem_iInf _).1 s.property j

/-- 概要：Moore 正規化単体の零番目の面は球面単体である。
方針：任意の面と零番目の面を交換すると正の面が現れる。
規約：chain 境界 d₀。使われ方：境界部分加群の定義。 -/
def sphereBoundaryMap (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelModule W (n + 2) →ₗ[S] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule W n where
  toFun s := ⟨W.δ 0 s.val, (Submodule.mem_iInf _).2 (fun j => by
    have h := congrArg (fun f => f s.val) (W.δ_comp_δ (Fin.zero_le j))
    change W.δ (0 : Fin (n + 2)) (W.δ j.succ s.val) =
      W.δ j (W.δ (0 : Fin (n + 3)) s.val) at h
    rw [mooreKernelModule_face, map_zero] at h
    exact h.symm)⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- 概要：球面単体の退化の二つの隣接面は元の単体で、他の面は零。
方針：四つの面・退化恒等式で場合分けする。
規約：任意の退化添字。使われ方：ホモトピー関係と群法則の線形計算。 -/
lemma sphericalModule_degeneracy_face {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule W n)
    (i : Fin (n + 2)) (j : Fin (n + 3)) :
    W.δ j (W.σ i s.val) = if j = i.castSucc then s.val else if j = i.succ then s.val else 0 := by
  by_cases h₁ : j = i.castSucc
  · subst j
    simp only [ite_true]
    exact congrArg (fun f => f s.val) W.δ_comp_σ_self
  by_cases h₂ : j = i.succ
  · subst j
    simp only [h₁, ite_false, ite_true]
    exact congrArg (fun f => f s.val) W.δ_comp_σ_succ
  simp only [h₁, h₂, ite_false]
  by_cases hj : j < i.castSucc
  · have hi : i ≠ 0 := by intro h; subst i; simp at hj
    let j' : Fin (n + 2) := j.castLT (by omega)
    have he₁ : (i.pred hi).succ = i := Fin.succ_pred i hi
    have he₂ : j'.castSucc = j := by ext; rfl
    have h := W.δ_comp_σ_of_le (i := j') (j := i.pred hi) (by
      have hval := congrArg Fin.val he₁
      simp only [Fin.val_succ] at hval
      dsimp only [j']
      simp only [Fin.le_def, Fin.val_castLT, Fin.val_castSucc]
      simp only [Fin.lt_def, Fin.val_castSucc] at hj
      omega)
    rw [he₁, he₂] at h
    have hv := congrArg (fun f => f s.val) h
    change W.δ j (W.σ i s.val) = W.σ (i.pred hi) (W.δ j' s.val) at hv
    rw [sphericalModule_face, map_zero] at hv
    exact hv
  · have hij : i.succ < j := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff] at hj h₁ h₂ ⊢
      omega
    have h := W.δ_comp_σ_of_gt' hij
    have hv := congrArg (fun f => f s.val) h
    simp only [ModuleCat.comp_apply] at hv
    rw [sphericalModule_face, map_zero] at hv
    exact hv

end SerrePositivity.InfinityCategories.Project.DerivedCategories
