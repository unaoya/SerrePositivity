module

public import SerrePositivity.KST.DerivedGeometry.AcyclicSubobjectExtension

/-!
概要：小さい試験商を加える工程を部分対象格子全体の拡大関数にする。
方針：真の非輪状部分対象では証明済みの拡大を選び、それ以外は全体を返す。
規約：零から始まる超限反復では非輪状性を別途帰納的に証明する。
使われ方：Stacks Lemma 19.12.3、TT §3・§8、Toën §3.2 の連続超限分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (hG : IsSeparator G) (M : CochainComplex C ℤ) (hM : M.Acyclic)

open scoped Classical in
/--
概要：各真部分対象を真に大きくする、非輪状部分対象上の小さい試験商の拡大関数。
方針：実際に証明した拡大の存在から選択する。
規約：非輪状でない部分対象では全体を返す。
使われ方：Stacks 19.12.3、TT §3 の部分対象格子上の超限反復。
-/
def largerAcyclicSubobject (S : Subobject M) : Subobject M :=
  if h : S = ⊤ then ⊤ else if hS : (S : CochainComplex C ℤ).Acyclic then
    (exists_larger_acyclic_subobject G hG M hM S hS h).choose else ⊤

/--
概要：拡大関数は全体を保つ。
方針：定義の全体の場合を使う。
規約：格子の最大元。
使われ方：Stacks 19.12.3、TT §3 の超限反復の停止判定。
-/
lemma largerAcyclicSubobject_top : largerAcyclicSubobject G hG M hM ⊤ = ⊤ := by
  classical
  rw [largerAcyclicSubobject, dite_eq_left rfl]

/--
概要：真の部分対象は拡大関数で真に大きくなる。
方針：非輪状の場合は存在定理、それ以外は全体への真の包含を使う。
規約：格子全体の主張。
使われ方：Stacks 19.12.3、TT §3 の小さい整列長での全体への到達。
-/
lemma lt_largerAcyclicSubobject (S : Subobject M) (hne : S ≠ ⊤) :
    S < largerAcyclicSubobject G hG M hM S := by
  classical
  rw [largerAcyclicSubobject, dite_eq_right hne]
  split_ifs with hS
  · exact (exists_larger_acyclic_subobject G hG M hM S hS hne).choose_spec.choose
  · exact lt_top_iff_ne_top.mpr hne

/--
概要：各部分対象は拡大後の部分対象に含まれる。
方針：全体か真の部分対象かで分ける。
規約：拡大関数自体の単調性は要求しない。
使われ方：Stacks 19.12.3、TT §3 の反復列の単調性。
-/
lemma le_largerAcyclicSubobject (S : Subobject M) : S ≤ largerAcyclicSubobject G hG M hM S := by
  by_cases h : S = ⊤
  · subst S
    rw [largerAcyclicSubobject_top]
  · exact (lt_largerAcyclicSubobject G hG M hM S h).le

/--
概要：非輪状な部分対象の拡大も非輪状。
方針：真の部分対象では存在証明の非輪状性、全体では元の複体の非輪状性を使う。
規約：超限反復の後続段階の不変条件。
使われ方：Stacks 19.12.3、TT §3 の超限分解の非輪状性。
-/
lemma largerAcyclicSubobject_acyclic (S : Subobject M) (hS : (S : CochainComplex C ℤ).Acyclic) :
    (largerAcyclicSubobject G hG M hM S : CochainComplex C ℤ).Acyclic := by
  classical
  by_cases h : S = ⊤
  · rw [h, largerAcyclicSubobject_top]
    exact fun n => (hM n).of_iso (asIso (⊤ : Subobject M).arrow).symm
  · rw [largerAcyclicSubobject, dite_eq_right h, dite_eq_left hS]
    exact (exists_larger_acyclic_subobject G hG M hM S hS h).choose_spec.choose_spec.choose_spec.1

end SerrePositivity.KST.DerivedGeometry
