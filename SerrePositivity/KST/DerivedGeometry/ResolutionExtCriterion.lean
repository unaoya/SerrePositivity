module

public import SerrePositivity.KST.DerivedGeometry.ResolutionTail
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
概要：完全な増大分解の Hom 完全性による Ext の制限の単射性の判定。
方針：サイクルの短完全列と分解の尾部による有限回の次元移動を使う。
規約：Ext の消滅を一般の分解に対する仮定として明示し、構造体のフィールドにはしない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 のアフィン消滅の帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/--
概要：完全な増大分解で正次数の Hom が完全なら Ext¹ の最初の制限は核が零。
方針：長完全列で核の類をサイクルからの射へ持ち上げ、その延長により接続像を消す。
規約：実際の Ext の合成と短完全列の拡張類を使う。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の次元移動の基底段階。
-/
lemma resolution_ext_one_eq_zero (K : ChainComplex A ℕ) (F : A) (hK : K.Acyclic)
    (hF : chainHomPositiveExact K F) (α : Ext (K.X 0) F 1)
    (hα : (Ext.mk₀ (K.d 1 0)).comp α (zero_add 1) = 0) : α = 0 := by
  let S := resolutionKernelShortComplex K
  have hS : S.ShortExact := resolutionKernelShortComplex_shortExact K hK
  obtain ⟨β, hβ⟩ := Ext.contravariant_sequence_exact₃ hS F α hα (n₀ := 0) (by omega)
  obtain ⟨g, hg⟩ := resolution_cycleHom_extend K (hK 1) hF (Ext.addEquiv₀ β)
  have he : (Ext.mk₀ S.f).comp (Ext.mk₀ g) (zero_add 0) = β := by
    rw [Ext.mk₀_comp_mk₀]
    exact (congrArg Ext.mk₀ hg).trans (Ext.mk₀_addEquiv₀_apply β)
  rw [← hβ, ← he]
  exact hS.extClass_comp_assoc (Ext.mk₀ g)

/--
概要：低次数の Ext が分解の各正次数の項で消えると最初の制限の核は零。
方針：Ext¹ の基底段階と第1サイクルによる尾部への次元移動で次数について帰納する。
規約：n+1 次数の Ext に対し、0<q<n+1 の消滅だけを使う。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Cartan 型消滅判定。
-/
lemma resolution_ext_eq_zero (n : ℕ) (K : ChainComplex A ℕ) (F : A) (hK : K.Acyclic)
    (hF : chainHomPositiveExact K F)
    (hvan : ∀ (i q : ℕ), 0 < q → q < n + 1 → Subsingleton (Ext (K.X (i + 1)) F q))
    (α : Ext (K.X 0) F (n + 1))
    (hα : (Ext.mk₀ (K.d 1 0)).comp α (zero_add (n + 1)) = 0) : α = 0 := by
  induction n generalizing K with
  | zero => exact resolution_ext_one_eq_zero K F hK hF α hα
  | succ n ih =>
    let S := resolutionKernelShortComplex K
    have hS : S.ShortExact := resolutionKernelShortComplex_shortExact K hK
    obtain ⟨β, hβ⟩ := Ext.contravariant_sequence_exact₃ hS F α hα
      (n₀ := n + 1) (by omega)
    have ht : (cycleResolutionTail K).Acyclic := cycleResolutionTail_acyclic K hK
    have hFt : chainHomPositiveExact (cycleResolutionTail K) F := chainHomPositiveExact_tail K hF
    have hvt (i q : ℕ) (hq : 0 < q) (hqn : q < n + 1) :
        Subsingleton (Ext ((cycleResolutionTail K).X (i + 1)) F q) := by
      simpa [cycleResolutionTail] using hvan (i + 1) q hq (by omega)
    have hβt : (Ext.mk₀ ((cycleResolutionTail K).d 1 0)).comp β (zero_add (n + 1)) = 0 := by
      have : Subsingleton (Ext ((cycleResolutionTail K).X 1) F (n + 1)) := by
        change Subsingleton (Ext (K.X 2) F (n + 1))
        exact hvan 1 (n + 1) (by omega) (by omega)
      exact Subsingleton.elim _ _
    have hz := ih (cycleResolutionTail K) ht hFt hvt β hβt
    rw [← hβ, hz]
    exact Ext.comp_zero _ _ _ _ _

/--
概要：分解の項の低次数 Ext 消滅のもとで増大に沿う Ext の制限は単射。
方針：証明済みの核の消滅を二つの類の差へ適用する。
規約：実際の加法準同型としての precomp を扱う。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 のアフィン消滅への入力。
-/
lemma resolution_ext_precomp_injective (n : ℕ) (K : ChainComplex A ℕ) (F : A)
    (hK : K.Acyclic) (hF : chainHomPositiveExact K F)
    (hvan : ∀ (i q : ℕ), 0 < q → q < n + 1 → Subsingleton (Ext (K.X (i + 1)) F q)) :
    Function.Injective ((Ext.mk₀ (K.d 1 0)).precomp F (zero_add (n + 1))) := by
  intro α β h
  apply sub_eq_zero.mp
  apply resolution_ext_eq_zero n K F hK hF hvan (α - β)
  change ((Ext.mk₀ (K.d 1 0)).precomp F (zero_add (n + 1))) (α - β) = 0
  rw [map_sub, h, sub_self]

end SerrePositivity.KST.DerivedGeometry
