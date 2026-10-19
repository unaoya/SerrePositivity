module

public import SerrePositivity.KST.DerivedGeometry.SubobjectIteration
public import SerrePositivity.KST.DerivedGeometry.ExactColimitAcyclic
public import Mathlib.Algebra.Homology.GrothendieckAbelian

/-!
概要：非輪状部分対象を保つ拡大関数の超限反復は全段階で非輪状。
方針：後続段階は拡大の保存性、極限段階は連続性と完全な filtered colimit を使う。
規約：各段階の非輪状性を帰納的に証明し、入力フィールドには置かない。
使われ方：Stacks Lemma 19.12.3、TT §3・§8、Toën §3.2 の非輪状複体の超限分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {M : CochainComplex C ℤ} (φ : Subobject M → Subobject M) (hφ : ∀ S, S ≤ φ S)
  (hA : ∀ S : Subobject M, (S : CochainComplex C ℤ).Acyclic → (φ S : CochainComplex C ℤ).Acyclic)
  (S₀ : Subobject M) (h₀ : (S₀ : CochainComplex C ℤ).Acyclic)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

include hA h₀ hφ
/--
概要：非輪状な初項からの拡大関数の超限反復は非輪状。
方針：整列帰納で極限の余極限へ非輪状性を移す。
規約：整列型は小さいものを使う。
使われ方：Stacks 19.12.3、TT §3 の試験商による全体の構成。
-/
lemma acyclic_subobject_transfiniteIterate (j : J) :
    ((transfiniteIterate φ j S₀ : Subobject M) : CochainComplex C ℤ).Acyclic := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa only [transfiniteIterate_bot] using h₀
  | succ j hj ih =>
    rw [transfiniteIterate_succ φ S₀ j hj]
    exact hA _ ih
  | isSuccLimit j hj ih =>
    have := hj.nonempty_Iio.to_subtype
    let F := subobjectIterationFunctor φ hφ S₀ J
    let D := (Set.principalSegIio j).monotone.functor ⋙ F
    have hD : ∀ a : Set.Iio j, (D.obj a).Acyclic := fun a => ih a.val a.property
    have hcolim : (colimit D).Acyclic := acyclic_colimit_of_exactColimits (.up ℤ) D hD
    let E : colimit D ≅ F.obj j := (colimit.isColimit D).coconePointUniqueUpToIso
      (F.isColimitOfIsWellOrderContinuous j hj)
    exact fun n => (hcolim n).of_iso E

end SerrePositivity.KST.DerivedGeometry
