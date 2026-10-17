module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtension
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # dg関手のHom写像による代表加群と制限代表加群の比較

## 概要
dg関手のHom写像による代表加群と制限代表加群の比較。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

omit [Small.{u} D] [Small.{u} E] in
lemma representableRestriction_naturality (d : D) (x y : Dᵒᵖ) :
    (representable A d).map x y ≫
      homPostcompose ((representable A d).obj x) (F.map y.unop d) =
    (restrictModule A D E F.op (representable A (F.obj d))).map x y ≫
      homPrecompose (F.map x.unop d) ((representable A (F.obj d)).obj (F.op.obj y)) := by
  apply hom_naturality_of_apply
  intro p f
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  rw [Cochain.comp_zero_cochain_v _ _ r n hn,
    Cochain.zero_cochain_comp_v _ _ r n hn]
  change (F.map y.unop d).f n
    (((representableMap A d x y).f p f).v r n hn h) =
    (((representableMap A (F.obj d) (F.op.obj x) (F.op.obj y)).f p
      ((F.map y.unop x.unop).f p f)).v r n hn ((F.map x.unop d).f r h))
  rw [representableMap_apply, representableMap_apply]
  exact F.map_forward A f h (by omega)

/-- 各成分がFのHom chain mapである全Hom自然な閉零比較。 -/
def representableRestrictionMap (d : D) :
    ForgetEnrichment.of (Complex A) (representable A d) ⟶
      (moduleRestriction A D E F.op).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj d))) :=
  moduleMorphismMk A D (fun x => F.map x.unop d)
    (representableRestriction_naturality A D E F d)

lemma representableRestrictionMap_eval (d x : D) :
    (moduleEvaluation A D x).map (representableRestrictionMap A D E F d) = F.map x d :=
  moduleMorphismMk_eval A D _ _ x

lemma representableRestrictionMap_quasiIso (hF : HomQuasiIso F) (d : D) :
    moduleQuasiIso A D (representableRestrictionMap A D E F d) := by
  intro x
  rw [representableRestrictionMap_eval]
  exact hF x d

end SerrePositivity.DifferentialGraded
