module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeBasis

/-! # 有限の依存関係に沿った高さの付け直し

概要：整礎な有限依存関係を保ちつつ、各点に指定された下限より高い高さを付ける。
方針：元の自然数値の高さによる整礎再帰で、依存先の最大値より一つ大きくする。
規約：依存先は有限集合で与える。使われ方：任意の射の cone の semibasis。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

variable {I : Type u} (rank : I → ℕ) (dependencies : I → Finset I)
  (lowering : ∀ i j, j ∈ dependencies i → rank j < rank i) (bound : I → ℕ)

/-- 概要：指定された下限と依存先の高さの両方を超える新しい高さ。
方針：元の高さを measure とする整礎再帰を使う。
規約：下限を含めた最大値に一を加える。使われ方：cone の始域側の高さ。 -/
def semifreeReheight : I → ℕ :=
  (measure rank).wf.fix (fun i rec =>
    max (bound i) ((dependencies i).attach.sup
      (fun j => rec j.val (lowering i j.val j.property))) + 1)

/-- 概要：付け直した高さは再帰式を満たす。
方針：整礎再帰の展開則を使う。規約：有限の依存先に対する最大値。
使われ方：下限と依存先それぞれとの不等式の証明。 -/
theorem semifreeReheight_eq (i : I) :
    semifreeReheight rank dependencies lowering bound i =
      max (bound i) ((dependencies i).attach.sup
        (fun j => semifreeReheight rank dependencies lowering bound j.val)) + 1 := by
  exact WellFounded.fix_eq (measure rank).wf _ i

/-- 概要：新しい高さは指定された下限より真に大きい。
方針：再帰式の最大値は下限以上である。
規約：下限には任意の自然数値関数を許す。使われ方：cone の写像成分の高さ制御。 -/
theorem bound_lt_semifreeReheight (i : I) :
    bound i < semifreeReheight rank dependencies lowering bound i := by
  rw [semifreeReheight_eq]
  exact lt_of_le_of_lt (Nat.le_max_left _ _) (Nat.lt_succ_self _)

/-- 概要：新しい高さも依存先へ移ると真に下がる。
方針：依存先の高さは有限な最大値以下であり、親の高さはその最大値より大きい。
規約：元の依存関係の降下性のみを使う。使われ方：cone の微分成分の高さ制御。 -/
theorem semifreeReheight_dependency_lt (i j : I) (h : j ∈ dependencies i) :
    semifreeReheight rank dependencies lowering bound j <
      semifreeReheight rank dependencies lowering bound i := by
  rw [semifreeReheight_eq rank dependencies lowering bound i]
  have hs := Finset.le_sup
    (f := fun k : {j // j ∈ dependencies i} =>
      semifreeReheight rank dependencies lowering bound k.val)
    (Finset.mem_attach (dependencies i) ⟨j, h⟩)
  exact lt_of_le_of_lt (hs.trans (Nat.le_max_right _ _)) (Nat.lt_succ_self _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis
open CategoryTheory _root_.SerrePositivity.DifferentialGraded
variable {S : Type u} [CommRing S] {P Q : Complex S}
  (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S P)

/-- 概要：基底元の微分に現れる基底元を次数も含めて有限集合にまとめる。
方針：微分の基底展開の台を次数付きの直和型へ埋め込む。
規約：添字は全整数次数の直和型。使われ方：cone の高さの整礎再帰。 -/
def differentialDependencies (a : Σ k, B.Index k) : Finset (Σ k, B.Index k) :=
  (((B.basis (a.1 + 1)).repr ((P.d a.1 (a.1 + 1)) (B.basis a.1 a.2))).support).map
    (Function.Embedding.sigmaMk (a.1 + 1))

/-- 概要：微分の依存先では元の高さが真に下がる。
方針：台の埋め込みから元の semibasis の降下則へ戻す。
規約：すべての次数を同時に扱う。使われ方：整礎再帰の正当化。 -/
theorem differentialDependencies_lowering (a b : Σ k, B.Index k)
    (h : b ∈ B.differentialDependencies a) :
    B.height b.1 b.2 < B.height a.1 a.2 := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp h
  exact B.lowering a.1 a.2 j hj

variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S Q) (f : P ⟶ Q)

/-- 概要：射による基底元の像に現れる終域の高さの最大値。
方針：像の有限な基底展開の台に対して最大値を取る。
規約：像が零なら最大値は零。使われ方：cone の高さの下限。 -/
def imageHeightBound (a : Σ k, B.Index k) : ℕ :=
  ((C.basis a.1).repr ((f.f a.1) (B.basis a.1 a.2))).support.sup (C.height a.1)

/-- 概要：cone の始域側に使う付け直した高さ。
方針：微分の依存先と射の像の高さの双方を超える整礎再帰を使う。
規約：始域の元の高さは整礎性の証明に用いる。
使われ方：任意の射の cone の semibasis の高さ。 -/
def coneSourceHeight (k : ℤ) (i : B.Index k) : ℕ :=
  semifreeReheight (fun a : Σ k, B.Index k => B.height a.1 a.2)
    B.differentialDependencies B.differentialDependencies_lowering
    (B.imageHeightBound C f) ⟨k, i⟩

/-- 概要：射の像の基底展開に出る終域の高さは新しい始域の高さより低い。
方針：像の台の最大値と新しい高さの下限則を組み合わせる。
規約：射が filtration を保存することは仮定しない。
使われ方：cone 微分の終域成分の降下性。 -/
theorem image_lt_coneSourceHeight (k : ℤ) (i : B.Index k) (j : C.Index k)
    (h : j ∈ ((C.basis k).repr ((f.f k) (B.basis k i))).support) :
    C.height k j < B.coneSourceHeight C f k i :=
  lt_of_le_of_lt (Finset.le_sup h)
    (bound_lt_semifreeReheight (fun a : Σ k, B.Index k => B.height a.1 a.2)
      B.differentialDependencies B.differentialDependencies_lowering
      (B.imageHeightBound C f) ⟨k, i⟩)

/-- 概要：微分の依存先では新しい始域の高さも真に下がる。
方針：付け直した高さの依存先に対する降下則を使う。
規約：終域の高さと射の像は下限にだけ使う。
使われ方：cone 微分のシフトされた始域成分の降下性。 -/
theorem differential_lt_coneSourceHeight (k : ℤ) (i : B.Index k) (j : B.Index (k + 1))
    (h : j ∈ ((B.basis (k + 1)).repr ((P.d k (k + 1)) (B.basis k i))).support) :
    B.coneSourceHeight C f (k + 1) j < B.coneSourceHeight C f k i := by
  apply semifreeReheight_dependency_lt
  exact Finset.mem_map.mpr ⟨j, h, rfl⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis
