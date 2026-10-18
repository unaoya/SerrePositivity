module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeGenerator
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
概要：KST Def3.1 の外積代数の任意可換環上のスカラー拡大同型。
方針：両方向の写像を外積と代数 tensor の普遍性で構成し、生成元で逆元律を示す。
規約：2の可逆性を仮定しない。収縮微分との適合性は別工程。
使われ方：Koszul dg 代数の係数変更比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- 概要：変更後の生成加群の外積から元の外積の tensor への代数射。
方針：係数変更後の生成元の平方零性で ExteriorAlgebra.lift を使う。
規約：KST Def3.1。使われ方：基底変更同型の順写像。 -/
def exteriorToBaseChange : ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift S ⟨exteriorBaseChangeGenerator, exteriorBaseChangeGenerator_sq_zero⟩

/-- 概要：元の生成元を係数変更後の生成元へ送る代数射。
方針：m↦ι(1⊗m) を外積の普遍性で延長する。
規約：KST Def3.1。使われ方：逆基底変更写像を tensor へ延長する準備。 -/
def exteriorOfBaseChangeAux : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S (S ⊗[R] M) :=
  ExteriorAlgebra.lift R
    ⟨(ExteriorAlgebra.ι S).restrictScalars R ∘ₗ TensorProduct.mk R S M 1,
      fun _ => ExteriorAlgebra.ι_sq_zero _⟩

/-- 概要：元の外積の tensor から変更後の生成加群の外積への代数射。
方針：係数射と元の外積からの射を代数 tensor の普遍性で合わせる。
規約：KST Def3.1。使われ方：基底変更同型の逆写像。 -/
def exteriorOfBaseChange : S ⊗[R] ExteriorAlgebra R M →ₐ[S] ExteriorAlgebra S (S ⊗[R] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) exteriorOfBaseChangeAux
    (fun _ _ => Algebra.commutes _ _)

/-- 概要：元の生成元の像を計算する。
方針：外積の lift の生成元公式。
規約：KST Def3.1。使われ方：逆元律と微分比較。 -/
@[simp] theorem exteriorOfBaseChangeAux_ι (m : M) :
    exteriorOfBaseChangeAux (R := R) (S := S) (ExteriorAlgebra.ι R m) =
      ExteriorAlgebra.ι S ((1 : S) ⊗ₜ[R] m) :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

/-- 概要：順基底変更射の純粋生成元上の公式。
方針：外積の lift の生成元公式と tensor 線形写像を評価する。
規約：KST Def3.1。使われ方：逆元律と微分比較。 -/
@[simp] theorem exteriorToBaseChange_ι (s : S) (m : M) :
    exteriorToBaseChange (ExteriorAlgebra.ι S (s ⊗ₜ[R] m)) = s ⊗ₜ[R] ExteriorAlgebra.ι R m :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

/-- 概要：逆基底変更射の純粋生成元上の公式。
方針：代数 tensor の lift とスカラー作用を計算する。
規約：KST Def3.1。使われ方：逆元律と微分比較。 -/
@[simp] theorem exteriorOfBaseChange_tmul_ι (s : S) (m : M) :
    exteriorOfBaseChange (s ⊗ₜ[R] ExteriorAlgebra.ι R m) =
      ExteriorAlgebra.ι S (s ⊗ₜ[R] m) := by
  change algebraMap S (ExteriorAlgebra S (S ⊗[R] M)) s *
    exteriorOfBaseChangeAux (R := R) (S := S) (ExteriorAlgebra.ι R m) = _
  rw [exteriorOfBaseChangeAux_ι, ← Algebra.smul_def, ← map_smul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- 概要：順基底変更射と逆基底変更射の合成は恒等。
方針：代数 tensor と外積の生成元で比較する。
規約：KST Def3.1。使われ方：基底変更同型の逆元律。 -/
theorem exteriorToBaseChange_comp_of :
    (exteriorToBaseChange (R := R) (S := S) (M := M)).comp exteriorOfBaseChange =
      AlgHom.id S _ := by
  ext m
  simp

/-- 概要：逆基底変更射と順基底変更射の合成は恒等。
方針：外積の生成元と tensor の純粋生成元で比較する。
規約：KST Def3.1。使われ方：基底変更同型の逆元律。 -/
theorem exteriorOfBaseChange_comp_to :
    (exteriorOfBaseChange (R := R) (S := S) (M := M)).comp exteriorToBaseChange =
      AlgHom.id S _ := by
  ext m
  simp

/-- 概要：外積代数は任意の可換環へのスカラー拡大と可換。
方針：両方向の普遍写像と証明済みの逆元律を合わせる。
規約：KST Def3.1、2の可逆性不要。使われ方：Koszul dg 代数の底変更の代数部分。 -/
def exteriorBaseChangeEquiv :
    ExteriorAlgebra S (S ⊗[R] M) ≃ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  AlgEquiv.ofAlgHom exteriorToBaseChange exteriorOfBaseChange
    exteriorToBaseChange_comp_of exteriorOfBaseChange_comp_to

end SerrePositivity.KST.DerivedBlowup
