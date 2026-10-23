module

public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFiniteCover
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：有限順序上の simplicial replacement の末尾と最初の係数部分による pushout 分解。
方針：交わりの pullback、共同全射性、交わりの外での係数の単射性を各次数で確認する。
規約：通常の単体集合の pushout として構成し、係数の Kan 性は要求しない。
使われ方：Kerodon Remark 5.3.2.12、Theorem 5.3.5.7、scaffold 比較の有限次元の帰納法。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：有限順序上の simplicial replacement は末尾と最初の係数部分の pushout。
方針：組み立て射の底変換を pullback と表示し、各次数の被覆と像の外の単射性を使う。
規約：共通部分は末尾の nerve と F(0) の直積。
使われ方：Kerodon Remark 5.3.2.12、Theorem 5.3.5.7、scaffold の比較を末尾へ帰納する分解。 -/
lemma scaffoldFiniteReplacement_isPushout (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    IsPushout
      (simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft (scaffoldFiniteTail n)
        (simplicialReplacementInitialCoefficient F (scaffoldFiniteInitial (n + 1)))))
      (nerveMap (scaffoldFiniteTail n) ▷ F.obj (ULift.up 0))
      (simplicialReplacementBaseMap (scaffoldFiniteTail n) F)
      (simplicialReplacementInitialAssembly F (scaffoldFiniteInitial (n + 1))) := by
  have hp := simplicialReplacementAssembly_baseMap_isPullback (scaffoldFiniteTail n)
    (simplicialReplacementInitialCoefficient F (scaffoldFiniteInitial (n + 1)))
  have : Mono (simplicialReplacementBaseMap (scaffoldFiniteTail n) F) :=
    (simplicialReplacementBaseMap_isPullback (scaffoldFiniteTail n) F).mono_fst_of_mono
  apply IsPushout.of_forall_isPushout_app
  intro d
  apply Types.isPushout_of_isPullback_of_mono' (hp.app d) (scaffoldFiniteReplacement_cover n F d)
  rintro ⟨σ, s⟩ ⟨δ, t⟩ hs _ he
  have hσ : σ = δ := congrArg Sigma.fst he
  subst δ
  have hz := scaffoldFiniteTail_complement_zero n (F.obj (ULift.up 0)) d (σ, s) hs
  have hσ0 : σ.obj 0 = ULift.up (0 : Fin (n + 2)) := ULift.ext hz
  have hto : (scaffoldFiniteInitial (n + 1)).to (σ.obj 0) = eqToHom hσ0.symm :=
    (scaffoldFiniteInitial (n + 1)).hom_ext _ _
  have heτ := eq_of_heq (Sigma.mk.inj he).2
  change SSet.yonedaEquiv.symm s ≫
      F.map ((scaffoldFiniteInitial (n + 1)).to (σ.obj 0)) =
    SSet.yonedaEquiv.symm t ≫ F.map ((scaffoldFiniteInitial (n + 1)).to (σ.obj 0)) at heτ
  rw [hto] at heτ
  have hst := (cancel_mono (F.map (eqToHom hσ0.symm))).1 heτ
  exact Prod.ext rfl (SSet.yonedaEquiv.symm.injective hst)

end SerrePositivity.InfinityCategories
