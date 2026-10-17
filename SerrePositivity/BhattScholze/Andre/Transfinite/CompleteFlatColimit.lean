module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlatEquiv
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import SerrePositivity.HomologicalAlgebra.TorExactColimits
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
/-! # 完全平坦性の余極限による保存

BS Thm 7.14（著者版 p.61）の極限段に使う、固定基底上の完全平坦性の保存。
Tor の対称性と正確な余極限との交換を使い、通常平坦性への置き換えは行わない。
忠実性は別の環論的課題として扱う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.BhattScholze.Andre.Transfinite
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
universe u v
set_option backward.isDefEq.respectTransparency false
/-- ## 概要
固定基底上の I 完全平坦加群の正確な余極限は I 完全平坦。
BS Thm 7.14（著者版 p.61）の極限段に必要な、Tor 消滅の保存を与える。

## 方針
I で消える任意の試験加群 N を固定し、Tor の対称性で余極限を第二変数へ移す。
Tor と正確な余極限の交換により、各段の消滅から極限の消滅を導く。

## 規約
I は任意。通常平坦性、p 正則性、有限生成性、遷移写像の単射性は要求しない。
余極限の正確性は HasExactColimitsOfShape として明示する。

## 使われ方
有向余極限およびその具体的加群モデルで完全平坦性を検証する。
-/
theorem isCompletelyFlat_colimit {R : Type u} [CommRing R] (I : Ideal R)
    {J : Type u} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    [HasExactColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (hF : ∀ j, IsCompletelyFlat I (F.obj j)) :
    IsCompletelyFlat I ↥(colimit F) := by
  intro N _ _ hN
  apply (isConcentratedInDegreeZero_derivedTensor_iff ↥(colimit F) N).mpr
  intro i hi
  let T := (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R N)
  let : PreservesColimitsOfShape J T := tor_preservesExactColimits _ i
  have hz (j : J) : IsZero (T.obj (F.obj j)) := by
    have : Subsingleton (TorModule R i (F.obj j) N) :=
      (isConcentratedInDegreeZero_derivedTensor_iff (F.obj j) N).mp (hF j N hN) i hi
    have : Subsingleton (TorModule R i N (F.obj j)) :=
      (torModuleComm (R := R) i N (F.obj j)).injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hzcol : IsZero (colimit (F ⋙ T)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro j
    exact (hz j).eq_of_src _ _
  have hzT : IsZero (T.obj (colimit F)) := IsZero.of_iso hzcol (preservesColimitIso T F)
  have := ModuleCat.subsingleton_of_isZero hzT
  exact (torModuleComm (R := R) i ↥(colimit F) N).injective.subsingleton

/-- ## 概要
I 完全平坦加群の有向余極限は、標準 Module.DirectLimit モデルでも I 完全平坦。
BS Thm 7.14（著者版 p.61）の極限段に用いる。

## 方針
ModuleCat の有向余極限の正確性と標準モデルの普遍性から、一般の保存定理を移送する。

## 規約
環・加群・添字は Type u。遷移写像の単射性と通常平坦性は不要。

## 使われ方
実際の代数の塔を加群の有向系として扱うときの完全平坦性を供給する。
-/
theorem isCompletelyFlat_moduleDirectLimit {R ι : Type u} [CommRing R] [Preorder ι]
    [Nonempty ι] [IsDirectedOrder ι]
    [DecidableEq ι] (I : Ideal R)
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (f : ∀ i j, i ≤ j → M i →ₗ[R] M j) [DirectedSystem M (fun i j h ↦ f i j h)]
    (hM : ∀ i, IsCompletelyFlat I (M i)) : IsCompletelyFlat I (Module.DirectLimit M f) := by
  let hAB : AB5OfSize.{0,u} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0,u,u,u} _
  let F := ModuleCat.directLimitDiagram M f
  let e : colimit F ≅ ModuleCat.of R (Module.DirectLimit M f) :=
    colimit.isoColimitCocone ⟨_, ModuleCat.directLimitIsColimit M f⟩
  exact isCompletelyFlat_of_linearEquiv I e.toLinearEquiv
    (isCompletelyFlat_colimit I F hM)

/-- ## 概要
I 完全平坦加群の有向余極限は、非交和を同一視する DirectLimit モデルでも I 完全平坦。
BS Thm 7.14（著者版 p.61）の極限段のモデル間の互換入口。

## 方針
Module.DirectLimit と非交和モデルの標準線形同型で移送する。

## 規約
環・加群・添字は Type u。遷移写像の単射性は不要。

## 使われ方
環・代数構造も持つ非交和モデルの極限に、この加群定理を適用する。
-/
theorem isCompletelyFlat_directLimit {R ι : Type u} [CommRing R] [Preorder ι]
    [Nonempty ι] [IsDirectedOrder ι] (I : Ideal R)
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (f : ∀ i j, i ≤ j → M i →ₗ[R] M j) [DirectedSystem M (fun i j h ↦ f i j h)]
    (hM : ∀ i, IsCompletelyFlat I (M i)) : IsCompletelyFlat I (_root_.DirectLimit M f) := by
  classical
  exact isCompletelyFlat_of_linearEquiv I (Module.DirectLimit.linearEquiv M f)
    (isCompletelyFlat_moduleDirectLimit I M f hM)

/-- 代数の非交和余極限と標準加群余極限の、元の係数作用を保つ比較。
BS Thm 7.14（著者版 p.61）の極限段で用いる。双方の普遍写像から互いに逆な線形写像を構成し、
遷移射の束の型が異なる場合にも、加群構造の定義的同一性を仮定せずに移送する。 -/
private def moduleDirectLimitEquivAlgebraDirectLimit {R ι : Type u} [CommRing R] [Preorder ι]
    [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[R] S j) [DirectedSystem S (fun i j h ↦ f i j h)] :
    let _ : DirectedSystem S (fun i j h ↦ (f i j h).toLinearMap) :=
      inferInstanceAs (DirectedSystem S (fun i j h ↦ f i j h))
    Module.DirectLimit S (fun i j h ↦ (f i j h).toLinearMap) ≃ₗ[R] (_root_.DirectLimit S f) := by
  classical
  dsimp only
  let g := fun i j h ↦ (f i j h).toLinearMap
  let a : Module.DirectLimit S g →ₗ[R] (_root_.DirectLimit S f) :=
    Module.DirectLimit.lift R ι S g (fun i ↦ (DirectLimit.Algebra.of S f i).toLinearMap)
      (fun i j h x ↦ DirectLimit.Algebra.of_f h x)
  let b : (_root_.DirectLimit S f) →ₗ[R] Module.DirectLimit S g :=
    DirectLimit.Module.lift R ι S f (fun i ↦ Module.DirectLimit.of R ι S g i)
      (fun i j h x ↦ Module.DirectLimit.of_f)
  refine { a with invFun := b, left_inv := ?_, right_inv := ?_ }
  · intro z
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    change b (a (Module.DirectLimit.of R ι S g i x)) = _
    rw [show a (Module.DirectLimit.of R ι S g i x) = DirectLimit.Module.of R ι S f i x from
      Module.DirectLimit.lift_of ..]
    rfl
  · intro z
    obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk f z
    have hz : DirectLimit.Module.of R ι S f i x = z := by with_unfolding_all exact hx.symm
    rw [← hz]
    change a (b (DirectLimit.Module.of R ι S f i x)) = _
    rw [show b (DirectLimit.Module.of R ι S f i x) = Module.DirectLimit.of R ι S g i x from
      rfl]
    exact Module.DirectLimit.lift_of ..

/-- ## 概要
I 完全平坦な R 代数の有向余極限は I 完全平坦である。
BS Thm 7.14（著者版 p.61）の極限段の通常環の余極限に適用する。

## 方針
代数準同型の同じ台写像を R 線形写像として扱い、加群余極限の保存定理を適用する。

## 規約
元の R 作用を保つ。忠実性と p 進完備化による保存は結論しない。

## 使われ方
p 完全忠実平坦な塔の極限で、完全平坦性の側だけを検証する。
-/
theorem isCompletelyFlat_algebraDirectLimit {R ι : Type u} [CommRing R] [Preorder ι]
    [Nonempty ι] [IsDirectedOrder ι] (I : Ideal R)
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[R] S j) [DirectedSystem S (fun i j h ↦ f i j h)]
    (hS : ∀ i, IsCompletelyFlat I (S i)) : IsCompletelyFlat I (_root_.DirectLimit S f) := by
  classical
  let : DirectedSystem S (fun i j h ↦ (f i j h).toLinearMap) :=
    inferInstanceAs (DirectedSystem S (fun i j h ↦ f i j h))
  exact isCompletelyFlat_of_linearEquiv I (moduleDirectLimitEquivAlgebraDirectLimit S f)
    (isCompletelyFlat_moduleDirectLimit I S (fun i j h ↦ (f i j h).toLinearMap) hS)

end SerrePositivity.BhattScholze.Andre.Transfinite
