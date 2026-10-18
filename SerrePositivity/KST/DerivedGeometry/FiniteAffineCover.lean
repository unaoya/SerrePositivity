module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# 有限アフィン被覆と交わりの有限細分

概要：準コンパクト開を実際の有限個のアフィン開で被覆する。
方針：Mathlib のアフィン開基底と準コンパクト性を使う。
規約：交わりのアフィン性を仮定しない。空被覆も許す。
使われ方：KST D4・§10-7、Bondal–van den Bergh Thm 3.1.1 の有限被覆帰納。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

/--
概要：指定開集合を被覆する有限アフィン開の族。
方針：アフィン開の有限集合とその合併の等式を保持する。
規約：重複を除いた有限添字を使い、空開の空被覆を許す。
使われ方：KST D4、TT §3・§8、§10-7 の降下と有限細分。
-/
structure FiniteAffineCoverOf (X : Scheme.{u}) (V : X.Opens) where
  /-- 概要：有限個のアフィン開。方針：有限集合を使う。規約：重複を除く。
  使われ方：KST D4 の局所係数環の添字。 -/
  charts : Finset X.affineOpens
  /-- 概要：指定開を被覆する条件。方針：開の上限で表す。規約：空の上限も許す。
  使われ方：TT §8 の有限被覆。 -/
  covers : ⨆ U ∈ charts, (U : X.Opens) = V

namespace FiniteAffineCoverOf

variable {X : Scheme.{u}} {V : X.Opens} (C : FiniteAffineCoverOf X V)

/--
概要：各チャートは被覆先の開に含まれる。
方針：被覆の上限等式を使う。
規約：チャートのアフィン性以外の分離条件は不要。
使われ方：KST D4、TT §3 の制限射。
-/
lemma chart_le (U : X.affineOpens) (hU : U ∈ C.charts) : (U : X.Opens) ≤ V := by
  rw [← C.covers]
  exact le_iSup_of_le U (le_iSup_of_le hU le_rfl)

/--
概要：被覆された開は準コンパクト。
方針：有限個のアフィン開のコンパクト性を有限合併へ移す。
規約：有限性は定義の有限集合から得る。
使われ方：Bondal–van den Bergh Thm 3.1.1 の被覆帰納の仮定。
-/
lemma isCompact (C : FiniteAffineCoverOf X V) : IsCompact (V : Set X) := by
  apply isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr
  exact ⟨↑C.charts, C.charts.finite_toSet, by simpa using C.covers.symm⟩

end FiniteAffineCoverOf

/--
概要：準コンパクト開には有限アフィン被覆が存在する。
方針：アフィン開基底から得た有限部分集合を有限集合へ移す。
規約：空開・空スキームを除外しない。
使われ方：KST D4・§10-7、Bondal–van den Bergh Thm 3.1.1 の初期被覆と細分。
-/
lemma nonempty_finiteAffineCoverOf {X : Scheme.{u}} (V : X.Opens)
    (hV : IsCompact (V : Set X)) : Nonempty (FiniteAffineCoverOf X V) := by
  classical
  obtain ⟨s, hs, heq⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hV
  exact ⟨⟨hs.toFinset, by simpa using heq.symm⟩⟩

/--
概要：準コンパクト性と有限アフィン被覆の存在の同値。
方針：アフィン開の有限合併のコンパクト性と有限部分被覆を組み合わせる。
規約：準分離性はこの同値に不要。
使われ方：KST D4、TT §8 の被覆の選択に依存しない仮定。
-/
lemma isCompact_iff_nonempty_finiteAffineCoverOf {X : Scheme.{u}} (V : X.Opens) :
    IsCompact (V : Set X) ↔ Nonempty (FiniteAffineCoverOf X V) :=
  ⟨nonempty_finiteAffineCoverOf V, fun ⟨C⟩ => C.isCompact⟩

/--
概要：準コンパクトスキームの有限アフィン被覆。
方針：全空間の準コンパクト性に有限部分被覆定理を適用する。
規約：選択する被覆は唯一とはしない。
使われ方：KST D4、Bondal–van den Bergh Thm 3.1.1 の有限被覆帰納。
-/
def finiteAffineCover (X : Scheme.{u}) [CompactSpace X] : FiniteAffineCoverOf X ⊤ :=
  Classical.choice (nonempty_finiteAffineCoverOf ⊤ isCompact_univ)

/--
概要：準分離スキームの二つのアフィン開の交わりには有限アフィン細分がある。
方針：準分離性で交わりを準コンパクトとし、有限被覆を選ぶ。
規約：交わり自体のアフィン性を要求しない。
使われ方：KST §10-7、TT §3・§8 の一般の qcqs スキーム上の MV と Čech 計算。
-/
def affineIntersectionCover {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U V : X.affineOpens) : FiniteAffineCoverOf X ((U : X.Opens) ⊓ (V : X.Opens)) :=
  Classical.choice (nonempty_finiteAffineCoverOf _
    ((quasiSeparatedSpace_iff_forall_affineOpens).mp inferInstance U V))

end SerrePositivity.KST.DerivedGeometry
