module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionComparisons
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlatPrincipalCompletion
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Composition
import all SerrePositivity.CommutativeAlgebra.CompletelyFlat.Composition

public import SerrePositivity.CommutativeAlgebra.DirectLimit
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeScalar
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTor
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
public import SerrePositivity.HomologicalAlgebra.ModuleScalarExtensionAnnihilator
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import SerrePositivity.HomologicalAlgebra.TorExactColimits
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.CommutativeAlgebra.Adic.ReductionScalarExtension
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Data.Set.Countable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine

/-!
# 完全平坦性・完備化と有向余極限（BS 著者版 Theorem 7.14 の極限段の一般補題）

## 概要
p 完全平坦・完全忠実平坦な射の合成と有向余極限での保存、剰余テンソルの余極限比較、非可算共終性をもつ余極限の p 進完備性と可算データの降下、有界ねじれ環の完備化、perfectoid 塔の非可算極限の完備性、distinguished 商の p 進完備化の perfectoid 性、有向余極限の mod p Frobenius と Frobenius 核。

## 方針
原典が「超限反復」の一言で済ませる部分の中身。André 固有の対象は使わない。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`OrdinaryRoots/Family`、`Transfinite/Limit`、`Transfinite/Tower`、`Variants/Auxiliary`。
-/

universe u v

/-! ## 通常の忠実平坦性の環余極限による保存

BS 著者版 Theorem 7.14（著者版 p.61）の極限段の忠実性に使う一般論。
固定基底の代数の有向系を扱い、単位元を保つ遷移射であることを利用する。
-/

@[expose] public noncomputable section FaithfullyFlatColimit

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {A ι : Type u} [CommRing A] [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[A] S j) [DirectedSystem S (fun i j h ↦ f i j h)]
/-- ## 概要
線形写像は I 倍の部分加群を I 倍の部分加群へ送る。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助計算。

## 方針
生成元と加法に関する帰納法を使う。

## 規約
基底イデアルの有限生成性を要求しない。

## 使われ方
有限段での基底イデアル倍の表示を後の段へ移す。
-/
private lemma map_ideal_smul {P Q : Type u} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (I : Ideal A) (g : P →ₗ[A] Q) {x : P}
    (hx : x ∈ I • (⊤ : Submodule A P)) : g x ∈ I • (⊤ : Submodule A Q) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr x _
    rw [g.map_smul]
    exact Submodule.smul_mem_smul hr (Submodule.mem_top)
  · intro x y hx hy
    rw [g.map_add]
    exact Submodule.add_mem _ hx hy

/-- ## 概要
代数の有向余極限で基底イデアルの倍として表される元は、一段でも同じイデアルの倍として表せる。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段で忠実性を反映するための補題。

## 方針
部分加群の生成に関する帰納法を用い、加法の場合には二段の共通上界を取る。

## 規約
基底イデアルは有限生成でなくてよく、遷移写像の単射性も不要。
係数は最初の基底 A 上の作用のまま扱う。

## 使われ方
単位元が基底イデアルの拡張に入る関係を有限段に降ろす。
-/
theorem directLimit_mem_ideal_smul (I : Ideal A) (x : _root_.DirectLimit S f)
    (hx : x ∈ I • (⊤ : Submodule A (_root_.DirectLimit S f))) :
    ∃ (i : ι) (y : S i), y ∈ I • (⊤ : Submodule A (S i)) ∧
      DirectLimit.Algebra.of S f i y = x := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr x _
    obtain ⟨i, y, hy⟩ := DirectLimit.exists_eq_mk f x
    refine ⟨i, r • y, Submodule.smul_mem_smul hr (Submodule.mem_top), ?_⟩
    rw [map_smul]
    congr 1
    with_unfolding_all exact hy.symm
  · intro x y hx hy
    obtain ⟨i, a, ha, hax⟩ := hx
    obtain ⟨j, b, hb, hby⟩ := hy
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, f i k hik a + f j k hjk b,
      Submodule.add_mem _ (map_ideal_smul I (f i k hik).toLinearMap ha)
        (map_ideal_smul I (f j k hjk).toLinearMap hb), ?_⟩
    rw [map_add, DirectLimit.Algebra.of_f, DirectLimit.Algebra.of_f, hax, hby]


/-- ## 概要
固定基底 A 上忠実平坦な代数の有向余極限は A 上忠実平坦である。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の剰余環に用いる一般論。

## 方針
通常平坦性は既存の余極限定理による。基底イデアルの拡張に単位元が入れば、
その表示と単位元との等式を有限段へ降ろし、その段の忠実平坦性から元のイデアルが単位イデアルと示す。

## 規約
遷移射は A 代数準同型で単位元を保つ。一般の加群準同型の有向系については主張しない。
単射性・Noether 性・非零性は要求しない。

## 使われ方
各段の剰余テンソル代数の通常の忠実平坦性から、剰余余極限の忠実平坦性を検証する。
p 完全忠実平坦性そのものや完備化による保存はまだ結論しない。
-/
theorem faithfullyFlat_algebraDirectLimit (hS : ∀ i, Module.FaithfullyFlat A (S i)) :
    Module.FaithfullyFlat A (_root_.DirectLimit S f) := by
  have (i : ι) : Module.Flat A (S i) := (hS i).toFlat
  apply (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A _).mpr
  refine ⟨directLimit_flat S f, ?_⟩
  intro I hI
  have hmem : (1 : _root_.DirectLimit S f) ∈ I • (⊤ : Submodule A (_root_.DirectLimit S f)) := by
    rw [hI]
    trivial
  obtain ⟨i, x, hx, heq⟩ := directLimit_mem_ideal_smul S f I 1 hmem
  have hz : DirectLimit.Module.of A ι S f i (x - 1) = 0 := by
    change DirectLimit.Ring.of S f i (x - 1) = 0
    rw [map_sub, map_one]
    change DirectLimit.Algebra.of S f i x - 1 = 0
    rw [heq, sub_self]
  obtain ⟨j, hij, hj⟩ := (DirectLimit.exists_eq_zero (f := f) ⟨i, x-1⟩).mp hz
  have he : f i j hij x = 1 := sub_eq_zero.mp (by simpa only [map_sub, map_one] using hj)
  have hm : (1 : S j) ∈ I • (⊤ : Submodule A (S j)) := by
    rw [← he]
    exact map_ideal_smul I (f i j hij).toLinearMap hx
  have htop : I.map (algebraMap A (S j)) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using hm
  have ht : I • (⊤ : Submodule A (S j)) = ⊤ := by
    rw [Ideal.smul_top_eq_map, htop]
    rfl
  exact ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A (S j)).mp (hS j)).2 I ht
end SerrePositivity.BhattScholze.Andre.Transfinite

end FaithfullyFlatColimit

/-! ## BoundedCompletion -/

@[expose] public noncomputable section BoundedCompletion

open SerrePositivity SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable (R : Type u) [CommRing R] (a : R) (n : ℕ) (b : R)
variable (hbound : ∃ N : ℕ, ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
include hbound in
/-- ## 概要
有界 a 冪ねじれを持つ環 R の通常 a 進完備化は、元の標準 R 作用に関して a 完全忠実平坦である。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の完備化を補足する。

## 方針
実主イデアル完備化 H0 の完全忠実平坦性を、通常完備化との R 代数同型で移す。

## 規約
a は任意の環の元である。a 正則性や Noether 性を仮定しない。
通常完備化と実導来完備化の比較は証明により構成する。

## 使われ方
perfectoid 塔の余極限の有界 p ねじれから、完備化後の完全忠実平坦性を導く。
-/
theorem isCompletelyFaithfullyFlat_adicCompletion_of_bounded_torsion :
    IsCompletelyFaithfullyFlat (Ideal.span {a}) (AdicCompletion (Ideal.span {a}) R) := by
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  exact isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {a})
    (boundedPrincipalCompletionAdicAlgEquiv R a hbound).toLinearEquiv
    (principalCompletionH0_isCompletelyFaithfullyFlat R a hbound)
end SerrePositivity.BhattScholze.Andre.Transfinite

end BoundedCompletion

/-! ## 完全平坦・完全忠実平坦な環準同型の合成

BS 著者版 Theorem 7.14（著者版 p.61）の超限塔で、各後続段から初期環までの性質を保つための一般論。
イデアルで消える任意の試験加群をスカラー拡大し、Tor と忠実性を二段階で検査する。
-/

@[expose] public noncomputable section Composition

namespace SerrePositivity.BhattScholze.Andre.Transfinite
open SerrePositivity CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- ## 概要
自然数 p に関する完全忠実平坦な二つの環準同型の合成は p 完全忠実平坦。
BS 著者版 Theorem 7.14（著者版 p.61）の後続段で step の出力を合成する入口。

## 方針
主イデアル (p) の環準同型による像が再び (p) であることから、一般の合成定理に帰着する。

## 規約
p の素数性はこの保存には不要。各作用は指定した環準同型の toAlgebra。

## 使われ方
元の step と同じ (p) の型を、拡張イデアルの型に変更せずに使う。
-/
theorem isCompletelyFaithfullyFlat_natCast_comp {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C]
    (φ : R →+* B) (ψ : B →+* C) (p : ℕ)
    (hB : letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) B)
    (hC : letI := ψ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) C) :
    letI := (ψ.comp φ).toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) C := by
  apply isCompletelyFaithfullyFlat_comp φ ψ (Ideal.span {(p : R)}) hB
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hC

end SerrePositivity.BhattScholze.Andre.Transfinite

end Composition

/-! ## 完全平坦性の余極限による保存

BS 著者版 Theorem 7.14（著者版 p.61）の極限段に使う、固定基底上の完全平坦性の保存。
Tor の対称性と正確な余極限との交換を使い、通常平坦性への置き換えは行わない。
忠実性は別の環論的課題として扱う。
-/

@[expose] public noncomputable section CompleteFlatColimit

namespace SerrePositivity.BhattScholze.Andre.Transfinite
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
set_option backward.isDefEq.respectTransparency false
/-- ## 概要
固定基底上の I 完全平坦加群の正確な余極限は I 完全平坦。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段に必要な、Tor 消滅の保存を与える。

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
BS 著者版 Theorem 7.14（著者版 p.61）の極限段に用いる。

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
BS 著者版 Theorem 7.14（著者版 p.61）の極限段のモデル間の互換入口。

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

/-- ## 概要
代数の非交和余極限と標準加群余極限の、元の係数作用を保つ比較。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助同型。

## 方針
双方の普遍写像から互いに逆な線形写像を構成する。

## 規約
遷移射の束の型が異なる場合にも、加群構造の定義的同一性を仮定しない。

## 使われ方
代数余極限へ完全平坦性を移送する。
-/
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
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の通常環の余極限に適用する。

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

end CompleteFlatColimit

/-! ## 剰余テンソルの余極限比較と完全忠実平坦性の保存

BS 著者版 Theorem 7.14（著者版 p.61）の極限段に用いる。固定基底の I 完全忠実平坦な代数の
有向余極限が I 完全忠実平坦であることを、元の R/I 作用のまま証明する。
-/

@[expose] public section ResidueTensorColimit

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace SerrePositivity.BhattScholze.Andre.Transfinite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A ι : Type u} [CommRing A] [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[A] S j) [DirectedSystem S (fun i j h ↦ f i j h)]
/-- ## 概要
代数の有向系の、元の基底上の加群図式。BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助対象。

## 方針
遷移代数準同型をそのまま線形写像とし、DirectedSystem の法則から函手の法則を示す。

## 規約
基底 A の作用を保つ。

## 使われ方
剰余テンソル函手に余極限の普遍性を適用する。
-/
def algebraModuleDiagram : ι ⥤ ModuleCat.{u} A where
  obj i := ModuleCat.of A (S i)
  map h := ModuleCat.ofHom (f _ _ h.le).toLinearMap
  map_id i := by
    ext x
    exact DirectedSystem.map_self (f := fun i j h ↦ f i j h) x
  map_comp hij hjk := by
    ext x
    exact (DirectedSystem.map_map (f := fun i j h ↦ f i j h) hij.le hjk.le x).symm

/-- ## 概要
非交和モデルの代数余極限を頂点とする加群余錐。BS 著者版 Theorem 7.14（著者版 p.61）の補助対象。

## 方針
標準包含の両立性から余錐を構成する。

## 規約
環と加群の余極限の台集合だけでなく、元の A 作用を指定する。

## 使われ方
スカラー拡大で保存される具体的余錐として使う。
-/
def algebraModuleCocone : Cocone (algebraModuleDiagram S f) where
  pt := ModuleCat.of A (_root_.DirectLimit S f)
  ι := {
    app := fun i ↦ ModuleCat.ofHom (DirectLimit.Module.of A ι S f i)
    naturality := by
      intro i j h
      ext x
      exact DirectLimit.Module.of_f }

/-- ## 概要
代数余極限の標準加群余錐は余極限である。BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助命題。

## 方針
非交和モデルの線形な普遍写像を使い、包含との合成で一意性を検査する。

## 規約
追加の平坦性や単射性を仮定しない。

## 使われ方
剰余スカラー拡大による余極限保存に使う。
-/
def algebraModuleIsColimit : IsColimit (algebraModuleCocone S f) where
  desc c := ModuleCat.ofHom (DirectLimit.Module.lift A ι S f (fun i ↦ (c.ι.app i).hom)
    (fun i j h x ↦ by
      have hc := congrArg (fun g ↦ g.hom x) (c.w (homOfLE h))
      exact hc))
  fac c i := by ext x; rfl
  uniq c m hm := by
    apply ModuleCat.hom_ext
    apply DirectLimit.Module.hom_ext
    intro i
    ext x
    exact congrArg (fun g ↦ g.hom x) (hm i)



open SerrePositivity
attribute [local instance] adicQuotientAlgebra
variable (I : Ideal A)
/-- ## 概要
基底イデアル I による各段の剰余環を結ぶ R/I 代数準同型。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の剰余図式を構成する。

## 方針
元の代数準同型の基底との両立性から、拡張イデアルを剰余する。

## 規約
剰余環の R/I 作用は既存の adicQuotientAlgebra。

## 使われ方
剰余環の有向余極限と、余極限の剰余テンソルを比較する。
-/
def residueTransition (i j : ι) (h : i ≤ j) :
    S i ⧸ I.map (algebraMap A (S i)) →ₐ[A ⧸ I] S j ⧸ I.map (algebraMap A (S j)) :=
  { Ideal.quotientMap (I.map (algebraMap A (S j))) (f i j h).toRingHom (by
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change f i j h (algebraMap A (S i) r) ∈ I.map (algebraMap A (S j))
      rw [(f i j h).commutes]
      exact Ideal.mem_map_of_mem (algebraMap A (S j)) hr) with
    commutes' := by
      intro q
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      change Ideal.Quotient.mk _ (f i j h (algebraMap A (S i) r)) =
        Ideal.Quotient.mk _ (algebraMap A (S j) r)
      rw [(f i j h).commutes] }
/-- ## 概要
剰余環の遷移写像は有向系を成す。BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助命題。

## 方針
剰余代表元上で元の有向系の恒等・合成法則を適用する。

## 規約
遷移写像は residueTransition で固定する。

## 使われ方
通常忠実平坦な剰余代数の有向余極限を構成する。
-/
instance residueDirectedSystem :
    DirectedSystem (fun i ↦ S i ⧸ I.map (algebraMap A (S i)))
      (fun i j h ↦ residueTransition S f I i j h) where
  map_self := by
    intro i x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (f i i le_rfl x) = Ideal.Quotient.mk _ x
    rw [DirectedSystem.map_self' f]
  map_map := by
    intro k j i hij hjk x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (f j k hjk (f i j hij x)) =
      Ideal.Quotient.mk _ (f i k (hij.trans hjk) x)
    rw [DirectedSystem.map_map (f := fun i j h ↦ f i j h)]

/-- ## 概要
加群図式の剰余スカラー拡大と、通常の剰余環図式は自然同型。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の比較。

## 方針
既存の quotientAlgebraScalarExtensionEquiv の自然性を、実際の剰余遷移写像と照合する。

## 規約
R/I 線形性を保持し、R 線形性だけに弱めない。

## 使われ方
スカラー拡大で保存した余極限を剰余環の余極限と同定する。
-/
def residueDiagramIso : algebraModuleDiagram S f ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I) ≅
    algebraModuleDiagram (fun i ↦ S i ⧸ I.map (algebraMap A (S i))) (residueTransition S f I) := by
  refine NatIso.ofComponents
    (fun i ↦ (quotientAlgebraScalarExtensionEquiv I (S i)).toModuleIso) ?_
  intro i j h
  have he : ModuleCat.ofHom (adicAlgebraReductionMap I (f i j h.le)) =
      ModuleCat.ofHom (residueTransition S f I i j h.le).toLinearMap := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change adicAlgebraReductionMap I (f i j h.le) (Ideal.Quotient.mk _ x) =
      residueTransition S f I i j h.le (Ideal.Quotient.mk _ x)
    rw [adicAlgebraReductionMap_mk]
    rfl
  simpa only [algebraModuleDiagram, Functor.comp_map, he] using
    quotientAlgebraScalarExtensionEquiv_naturality I (f i j h.le)


/-- ## 概要
有向余極限の通常剰余テンソルは、各段の通常剰余環の有向余極限と R/I 上線形同型。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の忠実性に用いる。

## 方針
加群余錐の普遍性をスカラー拡大で保存し、既存の剰余自然同型と組み合わせる。
元の剰余テンソルへの比較も既存の環商・テンソル同型で与える。

## 規約
元の R/I 作用を保つ。I は任意で、有限生成性・単射性・平坦性は要求しない。

## 使われ方
剰余環の余極限の忠実平坦性を、定義に現れる剰余テンソルへ移送する。
-/
def residueTensorDirectLimitEquiv :
    ((A ⧸ I) ⊗[A] (_root_.DirectLimit S f)) ≃ₗ[A ⧸ I]
      (_root_.DirectLimit (fun i ↦ S i ⧸ I.map (algebraMap A (S i)))
        (residueTransition S f I)) := by
  let E := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let F := algebraModuleDiagram S f
  let B := fun i ↦ S i ⧸ I.map (algebraMap A (S i))
  let g := residueTransition S f I
  let e1 : E.obj (ModuleCat.of A (_root_.DirectLimit S f)) ≅ colimit (F ⋙ E) :=
    (isColimitOfPreserves E (algebraModuleIsColimit S f)).coconePointUniqueUpToIso
      (colimit.isColimit _)
  let e2 : colimit (F ⋙ E) ≅ colimit (algebraModuleDiagram B g) :=
    HasColimit.isoOfNatIso (residueDiagramIso S f I)
  let e3 : colimit (algebraModuleDiagram B g) ≅ ModuleCat.of (A ⧸ I) (_root_.DirectLimit B g) :=
    colimit.isoColimitCocone ⟨_, algebraModuleIsColimit B g⟩
  let e : ((E.obj (ModuleCat.of A (_root_.DirectLimit S f))) : Type u) ≃ₗ[A ⧸ I]
      ((A ⧸ I) ⊗[A] (_root_.DirectLimit S f)) :=
    (quotientAlgebraScalarExtensionEquiv I (_root_.DirectLimit S f)).trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (_root_.DirectLimit S f) I).toLinearEquiv
  exact e.symm.trans (e1 ≪≫ e2 ≪≫ e3).toLinearEquiv

/-- ## 概要
固定基底上の I 完全忠実平坦な代数の有向余極限は I 完全忠実平坦。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の通常余極限について、完全忠実平坦性を保存する。

## 方針
完全平坦性の余極限保存と、通常剰余代数の忠実平坦性の余極限保存を、
剰余テンソルの R/I 線形比較で結ぶ。

## 規約
環と添字は Type u。I は任意。p 正則性・単射性・Noether 性は要求しない。
p 進完備化による保存はこの定理の結論に含めない。

## 使われ方
超限塔の極限段で、完備化前の環の完全忠実平坦性を供給する。
-/
theorem isCompletelyFaithfullyFlat_algebraDirectLimit
    (hS : ∀ i, IsCompletelyFaithfullyFlat I (S i)) :
    IsCompletelyFaithfullyFlat I (_root_.DirectLimit S f) := by
  refine ⟨SerrePositivity.BhattScholze.Andre.Transfinite.isCompletelyFlat_algebraDirectLimit
    I S f (fun i ↦ (hS i).1), ?_⟩
  let B := fun i ↦ S i ⧸ I.map (algebraMap A (S i))
  let g := residueTransition S f I
  have hB (i : ι) : Module.FaithfullyFlat (A ⧸ I) (B i) := by
    have := (hS i).2
    exact Module.FaithfullyFlat.of_linearEquiv (A ⧸ I) ((A ⧸ I) ⊗[A] S i)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (S i) I).toLinearEquiv
  have := SerrePositivity.BhattScholze.Andre.Transfinite.faithfullyFlat_algebraDirectLimit B g hB
  exact Module.FaithfullyFlat.of_linearEquiv (A ⧸ I) (_root_.DirectLimit B g)
    (residueTensorDirectLimitEquiv S f I)
end SerrePositivity.BhattScholze.Andre.Transfinite
end

end ResidueTensorColimit

/-! ## 非可算共終性の極限での可算データの降下

BS 著者版 Theorem 7.14（著者版 p.61）の超限反復で使う。原典の一文を補うため、
可算集合の上界という具体的な仮定を明示する。
-/

@[expose] public noncomputable section CountableDescent

namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
/-- ## 概要
添字の任意の可算集合が上界を持てば、余極限の可算族を一つの段へ同時に降ろせる。
BS 著者版 Theorem 7.14（著者版 p.61）の非可算共終性の極限段に用いる補助命題。

## 方針
各元の代表段を選び、それらの段全体の可算性から共通上界を取る。

## 規約
環と塔の添字は Type u。可算族の添字の宇宙は任意。遷移写像の単射性は不要。

## 使われ方
Cauchy 列や可算個の係数を一つの完備な段へ降ろす入口となる。
-/
theorem exists_stage_countable_family (hbound : ∀ s : Set ι, s.Countable → ∃ j, ∀ i ∈ s, i ≤ j)
    {κ : Type v} [Countable κ]
    (x : κ → Ring.DirectLimit R (fun i j h ↦ f i j h)) :
    ∃ (i : ι) (y : κ → R i), ∀ k, Ring.DirectLimit.of R (fun i j h ↦ f i j h) i (y k) = x k := by
  classical
  choose i y hy using fun k ↦ Ring.DirectLimit.exists_of (x k)
  obtain ⟨j, hj⟩ := hbound (Set.range i) (Set.countable_range i)
  refine ⟨j, fun k ↦ f (i k) j (hj (i k) ⟨k, rfl⟩) (y k), ?_⟩
  intro k
  rw [Ring.DirectLimit.of_f]
  exact hy k

end SerrePositivity.BhattScholze.Andre.Transfinite

end CountableDescent

/-! ## 非可算共終性をもつ有向余極限の p 進完備性

BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の極限段に必要な一般論。
可算集合の上界と単射な遷移写像から、完備化を挟まず余極限の完備性を示す。
-/

@[expose] public noncomputable section CountableCompletion

namespace SerrePositivity.BhattScholze.Andre.Transfinite

/-- ## 概要
主イデアル進合同は差の冪倍表示と同値。BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助計算。

## 方針
主イデアルの冪と単項生成イデアルの所属条件を書き換える。

## 規約
a は任意の可換環の元。

## 使われ方
合同を可算個の有限代数的な等式へ直す。
-/
private lemma principal_smodEq_iff {S : Type*} [CommRing S] (a x y : S) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • (⊤ : Submodule S S))] ↔
      ∃ z, x - y = a ^ n * z := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  rfl

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (p : ℕ)
local notation "L" => Ring.DirectLimit R (fun i j h ↦ f i j h)
local notation "ofL" => Ring.DirectLimit.of R (fun i j h ↦ f i j h)
/-- ## 概要
任意の可算添字集合が上界を持つ有向系で、遷移写像が単射かつ各段が p 進完備なら、
有向余極限も p 進完備である。BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助命題。

## 方針
分離性では全ての p 冪の割り算の証人を、前完備性では Cauchy 列と差の割り算の証人を、
可算データの降下により一段へ移す。その段から余極限への単射性で等式を反映する。

## 規約
p は任意の自然数でよく、素数性・p 正則性・非零性は不要。
環と塔の添字は Type u に留める。単射性を完全忠実平坦性から導く工程は別。

## 使われ方
非可算共終性の極限段と ω₁ の終段で、和集合の自動的な p 進完備性を検証する。
可算共終性の極限段の完備化はこの命題の対象外。
-/
theorem isAdicComplete_directLimit_of_countable_upperBound
    (hbound : ∀ s : Set ι, s.Countable → ∃ j, ∀ i ∈ s, i ≤ j)
    (hf : ∀ i j h, Function.Injective (f i j h))
    [∀ i, IsAdicComplete (Ideal.span {(p : R i)}) (R i)] :
    IsAdicComplete (Ideal.span {(p : L)}) L := by
  classical
  rw [isAdicComplete_iff]
  constructor
  · constructor
    intro x hx
    have hx' : ∀ n : ℕ, ∃ z : L, x = (p : L) ^ n * z := by
      intro n
      simpa only [sub_zero] using (principal_smodEq_iff (p : L) x 0 n).mp (hx n)
    choose d hd using hx'
    obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of x
    obtain ⟨j, d', hd'⟩ := exists_stage_countable_family R f hbound d
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have hdiv : ∀ n, f i k hik x = (p : R k) ^ n * f j k hjk (d' n) := by
      intro n
      apply Ring.DirectLimit.of_injective f hf k
      simpa only [map_mul, map_pow, map_natCast, Ring.DirectLimit.of_f, hd'] using hd n
    have hz : f i k hik x = 0 := by
      apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : R k)}) (R k))
      intro n
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        sub_zero, Ideal.mem_span_singleton]
      exact ⟨f j k hjk (d' n), hdiv n⟩
    rw [← Ring.DirectLimit.of_f hik x, hz, map_zero]
  · constructor
    intro a ha
    have hdiff : ∀ m n : ℕ, ∃ z : L, a m - a (m + n) = (p : L) ^ m * z := by
      intro m n
      exact (principal_smodEq_iff (p : L) (a m) (a (m+n)) m).mp (ha (Nat.le_add_right m n))
    choose d hd using hdiff
    obtain ⟨i, b, hb⟩ := exists_stage_countable_family R f hbound a
    obtain ⟨j, c, hc⟩ := exists_stage_countable_family R f hbound (Function.uncurry d)
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let b' : ℕ → R k := fun n ↦ f i k hik (b n)
    have heq : ∀ m n, b' m - b' (m+n) = (p : R k) ^ m * f j k hjk (c (m,n)) := by
      intro m n
      apply Ring.DirectLimit.of_injective f hf k
      simpa only [b', map_sub, map_mul, map_pow, map_natCast, Ring.DirectLimit.of_f,
        hb, hc, Function.uncurry_apply_pair] using hd m n
    obtain ⟨z, hz⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : R k)}) b' (by
      intro m n hmn
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      refine ⟨f j k hjk (c (m,n-m)), ?_⟩
      simpa only [Nat.add_sub_of_le hmn] using heq m (n-m))
    refine ⟨ofL k z, ?_⟩
    intro n
    obtain ⟨t, ht⟩ : ∃ t, b' n - z = (p : R k)^n * t := by
      have hmem := (SModEq.sub_mem).mp (hz n)
      rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at hmem
      exact Ideal.mem_span_singleton.mp hmem
    apply (principal_smodEq_iff (p : L) (a n) (ofL k z) n).mpr
    refine ⟨ofL k t, ?_⟩
    have he := congrArg (ofL k) ht
    simpa only [b', map_sub, map_mul, map_pow, map_natCast, Ring.DirectLimit.of_f, hb] using he
end SerrePositivity.BhattScholze.Andre.Transfinite

end CountableCompletion

/-! ## 完全忠実平坦な perfectoid 塔の非可算極限の完備性

BS 著者版 Theorem 7.14（著者版 p.61）。p ねじれを許す既存の単射性定理と
可算データの降下を結び、極限環が自動的に p 進完備であることを示す。
-/

@[expose] public noncomputable section PerfectoidLimitCompleteness

namespace SerrePositivity.BhattScholze.Andre.Transfinite
/-- ## 概要
perfectoid 環からの p 完全忠実平坦な環準同型は単射である。
BS 著者版 Theorem 7.14（著者版 p.61）の塔を単射な系として扱うための入口。

## 方針
非零の場合は p 進分離性と各冪剰余の忠実平坦性による既存の単射性定理を適用する。
零環の場合は元の一意性を使う。

## 規約
S の完備性、perfectoid 性、p 正則性は不要。作用は φ.toAlgebra そのもの。

## 使われ方
非可算共終性の極限での自動的な完備性を perfectoid 塔へ適用する。
-/
theorem injective_of_perfectoid_completelyFaithfullyFlat {R S : Type u} [CommRing R] [CommRing S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (φ : R →+* S)
    (hφ : let := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S) :
    Function.Injective φ := by
  rcases hR with hsub | ⟨_, hc, _⟩
  · exact fun _ _ _ ↦ hsub.elim _ _
  · let := hc
    let := φ.toAlgebra
    exact algebraMap_injective_of_completelyFaithfullyFlat_of_isHausdorff R S (p : R) hφ

/-- ## 概要
perfectoid 環の p 完全忠実平坦な有向系で、可算添字集合がすべて上界を持つなら、
余極限は p 進完備である。BS 著者版 Theorem 7.14（著者版 p.61）の非可算共終性の極限段。

## 方針
各段の完備性を定義から取り出し、完全忠実平坦性から遷移射の単射性を導いて、
可算データの降下による完備性定理を適用する。

## 規約
p ねじれと零環を許す。環と添字は Type u。Fontaine 核の単項性と極限写像の
完全忠実平坦性は、この定理の結論には含めない。

## 使われ方
ω₁ の終段や非可算共終性の極限段で、完備化を挟まず完備な環を得る。
-/
theorem isAdicComplete_directLimit_of_perfectoid_completelyFaithfullyFlat
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (hflat : ∀ i j h, let := (f i j h).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R i)}) (R j))
    (hbound : ∀ s : Set ι, s.Countable → ∃ j, ∀ i ∈ s, i ≤ j) :
    IsAdicComplete (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
      (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  have hc (i : ι) : IsAdicComplete (Ideal.span {(p : R i)}) (R i) := by
    rcases hR i with hsub | ⟨_, hc, _⟩
    · let := hsub
      infer_instance
    · exact hc
  let (i : ι) : IsAdicComplete (Ideal.span {(p : R i)}) (R i) := hc i
  apply isAdicComplete_directLimit_of_countable_upperBound R f p hbound
  intro i j h
  exact injective_of_perfectoid_completelyFaithfullyFlat p (hR i) (f i j h) (hflat i j h)
end SerrePositivity.BhattScholze.Andre.Transfinite

end PerfectoidLimitCompleteness

/-! ## Distinguished 商の通常 p 進完備化の perfectoid 性

BS 著者版 Theorem 3.10（著者版 p.32）と BS 著者版 Theorem 7.14（p.61）の極限段に用いる補助命題。
完全 δ 環の distinguished 商を通常に p 進完備化したものを、既存の実 PD 完備化の
完全 prism の商と、二つの普遍性から同一視する。
-/

@[expose] public noncomputable section PrismaticCompletion

namespace SerrePositivity.BhattScholze.Andre.Transfinite
open SerrePositivity SerrePositivity.BhattScholze SerrePositivity.DerivedCompletion
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- ## 概要
完全 δ 環 A の distinguished 元 d を核の生成元とする全射 A → T に対し、
T の通常の p 進完備化は perfectoid。BS 著者版 Theorem 3.10（著者版 p.32）、BS 著者版 Theorem 7.14（p.61）の補助命題。

## 方針
既存の実 PD 完備化から得る完全 prism の商 Q を使う。T の通常完備化 C と Q の間に、
通常完備化と実 PD 完備化の普遍性から互いに逆な環準同型を構成する。
Q の perfectoid 性を、得られた環同型で C へ移す。

## 規約
T の p 正則性・被約性・有界ねじれ・完備性は仮定しない。
通常完備化を実導来完備化と無条件に同一視せず、実際の二つの環普遍性を照合する。

## 使われ方
perfectoid 塔の未完備余極限を、完全 δ 環の distinguished 商として表示した後、
その p 進完備化の perfectoid 性を得る。
-/
theorem isIntegralPerfectoid_adicCompletion_of_distinguished_kernel {p : ℕ} [Fact p.Prime]
    {A T : Type u} [CommRing A] [CommRing T]
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d)
    (q₀ : A →+* T) (hq₀ : Function.Surjective q₀)
    (hk₀ : RingHom.ker q₀ = Ideal.span {d}) :
    IsIntegralPerfectoid (AdicCompletion (Ideal.span {(p : T)}) T) p := by
  let I : Ideal T := Ideal.span {(p : T)}
  let C := AdicCompletion I T
  let k : T →+* C := algebraMap T C
  have hI : I.FG := Submodule.fg_span (Set.toFinite _)
  let : IsAdicComplete I C := AdicCompletion.isAdicComplete hI
  have hmap : I.map k = Ideal.span {(p : C)} := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z : C ↦ Ideal.span {z}) (map_natCast k p)
  let : IsAdicComplete (Ideal.span {(p : C)}) C := by
    rw [← hmap]
    exact (IsAdicComplete.map_algebraMap_iff (I := I) (S := C) (M := C)).mpr inferInstance
  let := pdCompletionCommRing A p d
  let H := PDCompletionH0 A p d
  let j := pdCompletionUnit A p d
  let Q := H ⧸ Ideal.span {j d}
  let q : H →+* Q := Ideal.Quotient.mk _
  let : IsAdicComplete (Ideal.span {(p : Q)}) Q :=
    perfectDeltaPDPrism_quotient_isAdicComplete D hD d hd
  have hpQ := isModuleComplete_of_isAdicComplete Q (p : Q) (ModuleCat.of Q Q)
  have hqd : q (j d) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hz (B : Type u) [CommRing B] : IsModuleComplete B (0 : B) (ModuleCat.of B B) :=
    isModuleComplete_of_pow_smul_zero B 0 _ 1 (by simp)
  have hdQ : IsModuleComplete Q ((q.comp j) d) (ModuleCat.of Q Q) := hqd ▸ hz Q
  let f : A →+* C := k.comp q₀
  have hq₀d : q₀ d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hk₀]
    exact Ideal.mem_span_singleton_self _
  have hfd : f d = 0 := by
    change k (q₀ d) = 0
    rw [hq₀d, map_zero]
  have hpC := isModuleComplete_of_isAdicComplete C (p : C) (ModuleCat.of C C)
  have hdC : IsModuleComplete C (f d) (ModuleCat.of C C) := hfd ▸ hz C
  obtain ⟨g, hg, _⟩ := existsUnique_pdCompletionRingHom A p d C f hpC hdC
  have hgd : g (j d) = 0 := (RingHom.congr_fun hg d).trans hfd
  let b : Q →+* C := Ideal.Quotient.lift _ g (by
    change Ideal.span {j d} ≤ RingHom.ker g
    exact (Ideal.span_singleton_le_iff_mem _).mpr hgd)
  have hb : b.comp q = g := Ideal.Quotient.lift_comp_mk _ _ _
  have hfactor : RingHom.ker q₀ ≤ RingHom.ker (q.comp j) := by
    rw [hk₀]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hqd
  let t : T →+* Q := q₀.liftOfSurjective hq₀ ⟨q.comp j, hfactor⟩
  have ht : t.comp q₀ = q.comp j := q₀.liftOfSurjective_comp hq₀ _
  let := t.toAlgebra
  have hmapT : I.map (algebraMap T Q) = Ideal.span {(p : Q)} := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z : Q ↦ Ideal.span {z}) (map_natCast (algebraMap T Q) p)
  let : IsAdicComplete I Q := by
    apply (IsAdicComplete.map_algebraMap_iff (I := I) (S := Q) (M := Q)).mp
    rw [hmapT]
    infer_instance
  let i := adicCompletionToCompleteAlgebra T I hI Q
  have hi : i.toRingHom.comp k = t := by
    ext r
    exact i.commutes r
  let ba : Q →ₐ[T] C :=
    { b with
      commutes' := by
        intro r
        obtain ⟨a, rfl⟩ := hq₀ r
        change b (t (q₀ a)) = k (q₀ a)
        have hta := RingHom.congr_fun ht a
        change t (q₀ a) = q (j a) at hta
        rw [hta]
        have hba := RingHom.congr_fun hb (j a)
        change b (q (j a)) = g (j a) at hba
        rw [hba]
        exact RingHom.congr_fun hg a }
  have hbi : b.comp i.toRingHom = RingHom.id C := by
    exact congrArg AlgHom.toRingHom (adicCompletion_algHom_ext T I hI C
      (ba.comp i) (AlgHom.id T C))
  have hib : i.toRingHom.comp b = RingHom.id Q := by
    apply Ideal.Quotient.ringHom_ext
    change (i.toRingHom.comp b).comp q = (RingHom.id Q).comp q
    rw [RingHom.comp_assoc, hb, RingHom.id_comp]
    apply pdCompletionRingHom_ext A p d Q (q.comp j) hpQ hdQ
    · ext a
      have hga := RingHom.congr_fun hg a
      change g (j a) = k (q₀ a) at hga
      change i (g (j a)) = q (j a)
      rw [hga]
      have hia := RingHom.congr_fun hi (q₀ a)
      change i (k (q₀ a)) = t (q₀ a) at hia
      rw [hia]
      exact RingHom.congr_fun ht a
    · rfl
  let e : Q ≃+* C :=
    { b with invFun := i, left_inv := RingHom.congr_fun hib, right_inv := RingHom.congr_fun hbi }
  have hQ : IsIntegralPerfectoid Q p :=
    OrientedPrism.quotient_isIntegralPerfectoid (perfectDeltaPDPrism D hD d hd)
      (perfectDeltaPDPrism_isPerfect D hD d hd)
  exact isIntegralPerfectoid_of_ringEquiv p e hQ

end SerrePositivity.BhattScholze.Andre.Transfinite

end PrismaticCompletion

/-! ## CompletionUniversal -/

@[expose] public noncomputable section CompletionUniversal

open SerrePositivity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {R S : Type u} [CommRing R] [CommRing S] (p : ℕ)
/-- ## 概要
p 進完備な環 S への任意の環射 R→S を、R の通常 p 進完備化からの環射へ延長する。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段で用いる普遍性の補助命題。

## 方針
R の作用を元の環射から定め、p 主イデアルの写像を計算して、既存の代数完備化の普遍性を使う。

## 規約
p は任意の自然数。p 正則性・Noether 性・元環の完備性は要求しない。

## 使われ方
p 完全忠実平坦な perfectoid 代数の圏の余極限の普遍性を検証する。
-/
def natAdicCompletionLift (q : R →+* S) (hc : IsAdicComplete (Ideal.span {(p : S)}) S) :
    AdicCompletion (Ideal.span {(p : R)}) R →+* S := by
  let := q.toAlgebra
  let : IsAdicComplete (Ideal.span {(p : R)}) S := by
    apply (IsAdicComplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := S) (M := S)).mp
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hc
  exact (adicCompletionToCompleteAlgebra R (Ideal.span {(p : R)})
    (Submodule.fg_span (Set.toFinite _)) S).toRingHom
/-- ## 概要
p 進完備化からの標準延長は、元の R の各標準像上で与えられた環射と一致する。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段で用いる普遍性の補助命題。

## 方針
元の環射が定める代数構造を局所導入し、既存の標準延長の係数像の公式を使う。

## 規約
p は任意の自然数。p 正則性・Noether 性・元環の完備性は要求しない。

## 使われ方
p 完全忠実平坦な perfectoid 代数の圏の余極限の普遍性を検証する。
-/
theorem natAdicCompletionLift_of (q : R →+* S) (hc : IsAdicComplete (Ideal.span {(p : S)}) S)
    (r : R) : natAdicCompletionLift p q hc
      (algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) r) = q r := by
  let := q.toAlgebra
  let : IsAdicComplete (Ideal.span {(p : R)}) S := by
    apply (IsAdicComplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := S) (M := S)).mp
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hc
  exact adicCompletionToCompleteAlgebra_of R (Ideal.span {(p : R)}) _ S r
/-- ## 概要
p 進完備な環への二つの環射が、完備化前の元の環の標準像上で一致すれば、両環射は一致する。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段で用いる普遍性の補助命題。

## 方針
共通の元の環射により終域の代数構造を定め、両射をその上の代数射にして既存の一意性を使う。

## 規約
p は任意の自然数。p 正則性・Noether 性・元環の完備性は要求しない。

## 使われ方
p 完全忠実平坦な perfectoid 代数の圏の余極限の普遍性を検証する。
-/
theorem natAdicCompletion_ringHom_ext (hc : IsAdicComplete (Ideal.span {(p : S)}) S)
    (f g : AdicCompletion (Ideal.span {(p : R)}) R →+* S)
    (h : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g := by
  let q := f.comp (algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R))
  let := q.toAlgebra
  let : IsAdicComplete (Ideal.span {(p : R)}) S := by
    apply (IsAdicComplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := S) (M := S)).mp
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hc
  let fa : AdicCompletion (Ideal.span {(p : R)}) R →ₐ[R] S :=
    { f with commutes' := fun r ↦ rfl }
  let ga : AdicCompletion (Ideal.span {(p : R)}) R →ₐ[R] S :=
    { g with commutes' := fun r ↦ (RingHom.congr_fun h r).symm }
  exact congrArg AlgHom.toRingHom
    (adicCompletion_algHom_ext R (Ideal.span {(p : R)})
      (Submodule.fg_span (Set.toFinite _)) S fa ga)
end SerrePositivity.BhattScholze.Andre.Transfinite

end CompletionUniversal

/-! ## 有向余極限の mod p Frobenius

BS 著者版 Theorem 7.14（著者版 p.61）の極限段に必要な、剰余 Frobenius 全射性の保存。
Fontaine 核の単項性や完備化による保存とは区別する。
-/

@[expose] public noncomputable section ResidueFrobenius

namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    (p : ℕ) [Fact p.Prime]
omit [Fact p.Prime] in
/-- ## 概要
各段で mod p の p 乗写像が全射なら、有向余極限でも全射である。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段で perfectoid の一条件を保存する。

## 方針
余極限の元を一段に降ろし、その段で根を選ぶ。誤差の p 倍表示を環準同型で移送する。

## 規約
p ねじれと零環を許す。完備性や遷移写像の単射性は仮定しない。

## 使われ方
超限反復における極限段の剰余 Frobenius 条件の検証に使う。
-/
theorem directLimit_mod_p_pow_surjective (hF : ∀ i, Function.Surjective
    (fun x : R i ⧸ Ideal.span {(p : R i)} ↦ x ^ p)) :
    Function.Surjective (fun x :
      Ring.DirectLimit R (fun i j h ↦ f i j h) ⧸
        Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))} ↦ x ^ p) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of x
  obtain ⟨y, hy⟩ := hF i (Ideal.Quotient.mk _ x)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hd : y ^ p - x ∈ Ideal.span {(p : R i)} :=
    Ideal.Quotient.eq.mp (by simpa only [map_pow] using hy)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hd
  refine ⟨Ideal.Quotient.mk _ (Ring.DirectLimit.of R (fun i j h ↦ f i j h) i y), ?_⟩
  dsimp only
  rw [← map_pow]
  apply Ideal.Quotient.eq.mpr
  rw [← map_pow, ← map_sub]
  apply Ideal.mem_span_singleton.mpr
  refine ⟨Ring.DirectLimit.of R (fun i j h ↦ f i j h) i a, ?_⟩
  rw [ha, map_mul, map_natCast]

/-- ## 概要
perfectoid 環の有向余極限では mod p Frobenius が全射である。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の一条件。

## 方針
非零の場合は perfectoid の定義から全射性を取り出し、零環の場合は自明な根を選ぶ。

## 規約
余極限そのものの perfectoid 性や p 進完備性は結論しない。

## 使われ方
perfectoid 塔の極限段で、完備性と Fontaine 核を別途検証するときに使う。
-/
theorem directLimit_mod_p_pow_surjective_of_perfectoid
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) :
    Function.Surjective (fun x :
      Ring.DirectLimit R (fun i j h ↦ f i j h) ⧸
        Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))} ↦ x ^ p) := by
  apply directLimit_mod_p_pow_surjective R f p
  intro i
  rcases hR i with hsub | ⟨_, _, _, hF, _⟩
  · let := hsub
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact hF

end SerrePositivity.BhattScholze.Andre.Transfinite

end ResidueFrobenius

/-! ## Perfectoid 塔の未完備余極限の Frobenius 核

BS 著者版 Theorem 7.14（著者版 p.61）の極限段に必要な代数的条件を保存する。
原典で省略された極限操作の補助命題であり、Fontaine 核の単項性の判定を代用しない。
-/

@[expose] public noncomputable section FrobeniusKernelColimit

open SerrePositivity
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (fun i j h ↦ f i j h)]
local notation "L" => Ring.DirectLimit R (fun i j h ↦ f i j h)
local notation "ofL" => Ring.DirectLimit.of R (fun i j h ↦ f i j h)
/-- ## 概要
perfectoid 塔の一段で p=u*π^p を満たす π の像は、余極限でも p 乗がその像の p 乗で
割り切れる元を割り切る。BS 著者版 Theorem 7.14（著者版 p.61）の極限段の Frobenius 核計算。

## 方針
元と割り算の証人を共通の段へ降ろし、その等式が成立する後の段で
既存の perfectoid Frobenius 核定理を適用する。

## 規約
p ねじれと零環を許す。遷移写像の単射性・完全平坦性・完備性は不要。

## 使われ方
未完備余極限の mod π から mod π^p への Frobenius の単射性を検証する。
-/
theorem ringDirectLimit_frobenius_kernel_of_stage_root (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (i₀ : ι) (π : R i₀) (u : (R i₀)ˣ) (hp : (p : R i₀) = u * π ^ p)
    (x : L) (hx : x ^ p ∈ Ideal.span {(ofL i₀ π) ^ p}) : x ∈ Ideal.span {ofL i₀ π} := by
  obtain ⟨i, x₀, hx₀⟩ := Ring.DirectLimit.exists_of x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨j, c₀, hc₀⟩ := Ring.DirectLimit.exists_of c
  obtain ⟨k₀, h₀k₀, hik₀⟩ := exists_ge_ge i₀ i
  obtain ⟨k, hk₀k, hjk⟩ := exists_ge_ge k₀ j
  let h₀k := h₀k₀.trans hk₀k
  let hik := hik₀.trans hk₀k
  let y := f i k hik x₀
  let q := f i₀ k h₀k π
  let d := f j k hjk c₀
  have hzero : ofL k (y ^ p - q ^ p * d) = 0 := by
    simp only [map_sub, map_mul, map_pow]
    simp only [y, q, d, Ring.DirectLimit.of_f, hx₀, hc₀]
    exact sub_eq_zero.mpr hc
  obtain ⟨l, hkl, hl⟩ := Ring.DirectLimit.of.zero_exact hzero
  let φ := (f k l hkl).comp (f i₀ k h₀k)
  have hp' : (p : R l) = (Units.map φ.toMonoidHom u : R l) * (φ π) ^ p := by
    change (p : R l) = φ (u : R i₀) * (φ π) ^ p
    simpa only [map_natCast, map_mul, map_pow] using congrArg φ hp
  have hpow : (f k l hkl y) ^ p ∈ Ideal.span {(φ π) ^ p} := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨f k l hkl d, ?_⟩
    change (f k l hkl y) ^ p = (f k l hkl q) ^ p * f k l hkl d
    simpa only [map_sub, map_mul, map_pow, sub_eq_zero] using hl
  have hk := (hR l).frobenius_kernel_of_unit_root (R l) p (φ π)
    (Units.map φ.toMonoidHom u) hp' (f k l hkl y) hpow
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hk
  have hyl : ofL l (f k l hkl y) = x := by
    rw [Ring.DirectLimit.of_f]
    simpa only [y, Ring.DirectLimit.of_f] using hx₀
  have hql : ofL l (φ π) = ofL i₀ π := by
    change ofL l (f k l hkl (f i₀ k h₀k π)) = _
    rw [Ring.DirectLimit.of_f, Ring.DirectLimit.of_f]
  apply Ideal.mem_span_singleton.mpr
  refine ⟨ofL l b, ?_⟩
  rw [← hyl, hb, map_mul, hql]


/-- ## 概要
perfectoid 塔の一段の π の像について、余極限で x^p が (π^p) に入ることと
x が (π) に入ることは同値。BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助命題。

## 方針
一方向は有限段の Frobenius 核の移送、逆方向は π 倍表示を p 乗する。

## 規約
π は一段で p=u*π^p を満たすもの。余極限自体を perfectoid と仮定しない。

## 使われ方
完備化の開イデアル商を介して、Frobenius の核表示を完備化側へ移す準備となる。
-/
theorem ringDirectLimit_pow_mem_span_iff_of_stage_root (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (i₀ : ι) (π : R i₀) (u : (R i₀)ˣ) (hp : (p : R i₀) = u * π ^ p) (x : L) :
    x ^ p ∈ Ideal.span {(ofL i₀ π) ^ p} ↔ x ∈ Ideal.span {ofL i₀ π} := by
  refine ⟨ringDirectLimit_frobenius_kernel_of_stage_root R f p hR i₀ π u hp x, ?_⟩
  intro hx
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx
  apply Ideal.mem_span_singleton.mpr
  exact ⟨b ^ p, by rw [hb, mul_pow]⟩

/-- ## 概要
perfectoid 塔の未完備余極限には p=u*π^p を満たす π と単元 u が存在し、
mod p Frobenius は全射、かつ x^p∈(π^p) と x∈(π) は同値。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の代数的条件。

## 方針
任意の一段から π と単元を移し、剰余 Frobenius と核計算の余極限保存を合成する。

## 規約
零環を許す。余極限の p 進完備性と Fontaine 核の単項性は結論しない。

## 使われ方
完備化後の perfectoid 判定に必要な、完備化前の具体的根と Frobenius 条件を供給する。
-/
theorem ringDirectLimit_exists_frobenius_root_data (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) :
    ∃ (π : L) (u : Lˣ), (p : L) = u * π ^ p ∧
      Function.Surjective (fun x : L ⧸ Ideal.span {(p : L)} ↦ x ^ p) ∧
      ∀ x : L, x ^ p ∈ Ideal.span {π ^ p} ↔ x ∈ Ideal.span {π} := by
  let i₀ : ι := Classical.arbitrary ι
  have hr : ∃ (π : R i₀) (u : (R i₀)ˣ), (p : R i₀) = u * π ^ p := by
    rcases hR i₀ with hsub | ⟨_, _, hr, _⟩
    · exact ⟨0, 1, hsub.elim _ _⟩
    · exact hr
  obtain ⟨π, u, hp⟩ := hr
  refine ⟨ofL i₀ π, Units.map (ofL i₀).toMonoidHom u, ?_,
    directLimit_mod_p_pow_surjective_of_perfectoid R f p hR, ?_⟩
  · change (p : L) = ofL i₀ (u : R i₀) * (ofL i₀ π) ^ p
    simpa only [map_natCast, map_mul, map_pow] using congrArg (ofL i₀) hp
  · exact ringDirectLimit_pow_mem_span_iff_of_stage_root R f p hR i₀ π u hp

end SerrePositivity.BhattScholze.Andre.Transfinite

end FrobeniusKernelColimit
