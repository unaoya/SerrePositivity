module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurOperationRightUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurInputNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerOnes
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyGeneratorIso

/-!
模型。文献の定義との比較は後で
# Schur 代数の生成元への作用

概要：Berger–Moerdijk §1 の Schur 代数の arity ごとの生成射を、単位からの生成元に対する作用で表す。
方針：単位係数と一次の入力からなる同型で前合成し、全合成の右単位則を用いる。
規約：arity 零の生成射も含む。
使われ方：Schur 代数からの代数射が生成元上の値で一意に決まることを証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.TensorPowers.power
  SerrePositivity.SymmetricSequence SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurAction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurOperationGenerator

/-- 概要：Schur 代数の生成元へ n 入力演算を作用させると arity n の生成射になる（Berger–Moerdijk §1）。
方針：一次の入力に付く単位因子を同型で補い、単位係数を入れた Schur 演算の式を使う。
規約：全ての入力の生成元包含は同じ schurUnit。
使われ方：自由代数の普遍性の一意性と随伴の残りの逆律を導く。 -/
lemma schurAction_generators (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (n : ℕ) :
    (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (P.schurUnit K) n) ≫ P.schurAction K n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K n := by
  let D := fun _ : ℕ => 𝟙_ (Complex A) ⊗ power K 1
  let E := fun _ : ℕ => P.arity 1 ⊗ power K 1
  let w := (λ_ (power K 1)).hom ≫ (ρ_ K).hom
  let v := P.unit ▷ power K 1
  let G := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator K D (fun _ => w) n (fun _ => 1)
  have hw : IsIso w := by dsimp only [w]; infer_instance
  have hG : IsIso G := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_isIso K D (fun _ => w) (fun _ => hw) n (fun _ => 1)
  have hu : w ≫ P.schurUnit K = v ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K 1 := by
    dsimp only [w, v, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurUnit, oneIso]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_naturality D E (fun _ => w)
    (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K 1) (P.schurUnit K) (fun _ => v)
    (fun _ => hu) n (fun _ => 1)
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_reindex ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
    (fun r => P.arity r ⊗ power K r) (fun r => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K r)
    (fun _ : ℕ => 1) n (fun _ : Fin n => 1)
  change P.schurInputGenerator K n (fun _ => 1) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) E
      (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K 1) n (fun _ => 1) at hr
  rw [← hr] at hn
  have hg : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun _ : Fin n => (λ_ (power K 1)).hom) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun _ => 1)).hom ≫
      eqToHom (congrArg (power K) (by simp : (∑ _ : Fin n, 1) = n)) = G := by
    dsimp only [G, D, w]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_ones]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_asMap]
    rw [← reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap_comp n
      (fun _ : Fin n => (λ_ (power K 1)).hom) (fun _ => (ρ_ K).hom))]
  apply (cancel_epi (P.arity n ◁ G)).1
  rw [← whiskerLeft_comp_assoc, hn]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [P.schurInputGenerator_action, P.schurOperationGenerator_units, hg]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
