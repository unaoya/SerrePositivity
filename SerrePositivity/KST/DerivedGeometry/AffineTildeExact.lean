module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
概要：通常のアフィン tilde 関手の完全性を証明する。
方針：素点での局所化の単射性から任意の開上の切断の単射性を得る。
規約：加群の有限生成性・射影性は要求しない。
使われ方：Bondal–van den Bergh Thm 3.1.1、TT §3、Toën §3.2 のアフィン比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable (R : CommRingCat.{u})

/--
概要：加群準同型の単射性は tilde の任意の開上の切断でも保たれる。
方針：局所分数の各素点での値に局所化の単射性を適用する。
規約：切断の局所分数条件は元の tilde の定義を保持する。
使われ方：TT §3、Toën §3.2 の tilde の左完全性。
-/
lemma affineTilde_map_app_injective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Injective f.hom) (U : (Spec R).Opens) :
    Function.Injective (((tilde.functor R).map f).val.app (.op U)) := by
  intro x y h
  apply Subtype.ext
  funext p
  apply IsLocalizedModule.map_injective p.val.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl N) f.hom hf
  exact congrArg (fun z => z.val p) h

/--
概要：アフィン tilde 関手は単射を保つ。
方針：全ての開上の切断で単射なので、前層への忘却後に単射と判定する。
規約：構造層の加群層の元の射を使う。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン導来比較。
-/
instance affineTilde_preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves {M N} f _ := by
    have hf := (ModuleCat.mono_iff_injective f).mp inferInstance
    have : Mono (((SheafOfModules.forget (Spec R).ringCatSheaf).map
        ((tilde.functor R).map f))) := by
      exact PresheafOfModules.mono_of_injective
        (fun {U} => affineTilde_map_app_injective R f hf U.unop)
    exact (SheafOfModules.forget (Spec R).ringCatSheaf).mono_of_mono_map inferInstance

/--
概要：アフィン tilde 関手はコホモロジーを保つ。
方針：単射の保存と左随伴による余核の保存を使う。
規約：平坦性を追加の仮定として要求しない。
使われ方：TT §3、Toën §3.2 の係数 tilde の完全性への入力。
-/
instance affineTilde_preservesHomology : (tilde.functor R).PreservesHomology :=
  (tilde.functor R).preservesHomology_of_preservesMonos_and_cokernels

/--
概要：アフィン tilde 関手は有限極限を保つ。
方針：証明済みのコホモロジー保存から左完全性を得る。
規約：右完全性は既存の tilde の左随伴性から得る。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の完全関手の導来化。
-/
instance affineTilde_preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  (tilde.functor R).preservesFiniteLimits_of_preservesHomology

end SerrePositivity.KST.DerivedGeometry
