module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ModuleMittagLeffler
public import SerrePositivity.AlgebraicGeometry.FiniteBasisCoevaluation

/-!
概要：KST §5、Stacks 05DP・059X の積比較の単射性を有限基底の余評価テンソルへ適用する。
方針：各成分の消滅を積比較写像の自然性で積の消滅へ移す。
規約：任意の試験族を許し、実際の線形写像と余評価テンソルを使う。
使われ方：双対像の商を試験族として一様な有限後続段階を取る。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：Mittag–Leffler 加群への評価で各余評価成分が消えれば、双対係数写像の積で作った余評価テンソルも消える。
方針：テンソル積と積の比較の単射性を使い、各成分を自然性と余評価の成分公式で計算する。
規約：KST §5、Stacks 05DP・059X、基底のみ有限、試験族の添字は任意。
使われ方：双対像の商による成分ごとの消滅から、一様な後続段階を取る前の積の消滅。
-/
theorem mittagLeffler_basisMappedCoevaluationTensor_pi_eq_zero
    {R U M J : Type u} {ι : Type v} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup M] [Module R M] [Fintype ι]
    (P : J → Type u) [∀ j, AddCommGroup (P j)] [∀ j, Module R (P j)]
    (b : Module.Basis ι R U) (q : U →ₗ[R] M) (ε : ∀ j, Module.Dual R U →ₗ[R] P j)
    (hM : IsModuleMittagLeffler R M)
    (hε : ∀ j, q.rTensor (P j) (basisMappedCoevaluationTensor b (ε j)) = 0) :
    q.rTensor (∀ j, P j) (basisMappedCoevaluationTensor b (LinearMap.pi ε)) = 0 := by
  apply hM J P
  rw [map_zero]
  funext j
  rw [tensorPiRightHom_rTensor_apply, basisMappedCoevaluationTensor_piRightHom]
  exact hε j

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
