module
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# 非被約な自由整数単体的加群

概要：C(H)=ℤBH の非被約な自由加群の界面を作る。
方針：有限台整数関数で宇宙に依存しない自由加群関手を実現する。
規約：KST Appendix A、Definition A.3、Construction A.6。H_* 自体は定義しない。
使われ方：nerve の実ホモトピーを単体的加群のホモトピーへ移す。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory MonoidalCategory

/-- 概要：任意の宇宙の集合に自由整数加群を対応させる。
方針：Finsupp の変数の移送を使う。
規約：非被約。使われ方：KST Appendix A の ℤ(-)。 -/
def integerLinearization : Type u ⥤ ModuleCat.{u} ℤ where
  obj X := ModuleCat.of ℤ (X →₀ ℤ)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ f)

/-- 概要：自由整数加群の基底元。
方針：係数1の単項有限台関数。
規約：KST Appendix A の非被約な基底。使われ方：自由加群射の外延性。 -/
abbrev integerGenerator {X : Type u} (x : X) : integerLinearization.obj X :=
  Finsupp.single x 1

/-- 概要：自由化した写像は基底を対応する基底へ送る。
方針：Finsupp の変数の移送。
規約：KST Appendix A。使われ方：単体的自然性と両端条件の検証。 -/
@[simp] lemma integerLinearization_map_generator {X Y : Type u} (f : X ⟶ Y) (x : X) :
    integerLinearization.map f (integerGenerator x) = integerGenerator (f x) := by
  apply Finsupp.mapDomain_single

/-- 概要：自由整数加群からの射は基底上で決まる。
方針：有限台関数の普遍性と整数加群射の1での評価。
規約：KST Appendix A。使われ方：自由化したホモトピーの等式検証。 -/
lemma integerLinearization_hom_ext {X : Type u} {M : ModuleCat.{u} ℤ}
    {f g : integerLinearization.obj X ⟶ M}
    (h : ∀ x, f (integerGenerator x) = g (integerGenerator x)) : f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' (fun x ↦ LinearMap.ext_ring (h x)))

/-- 概要：単体的集合の非被約な自由整数単体的加群。
方針：各次数で自由整数加群を取る。
規約：KST Definition A.3 の C(H) は X=BH の場合。H_* は所有レーンから借りる。
使われ方：A.6 の実単体的加群ホモトピーの値域。 -/
abbrev linearizedSpace (X : SSet.{u}) : SimplicialObject (ModuleCat.{u} ℤ) :=
  X ⋙ integerLinearization

/-- 概要：自由整数単体的加群に誘導される射。
方針：自由化関手による右 whisker。
規約：KST Appendix A。使われ方：C(φ) の界面。 -/
abbrev linearizedSpaceMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    linearizedSpace X ⟶ linearizedSpace Y :=
  ((SimplicialObject.whiskering _ _).obj integerLinearization).map f

/-- 概要：実単体的ホモトピーを自由整数単体的加群へ移す。
方針：組合せ的な単体的ホモトピーを自由化関手で右 whisker する。
規約：KST Construction A.6。非被約な全次数ホモトピー。
使われ方：C(H) のホモトピーと正規化後の鎖ホモトピーへの入力。 -/
def linearizedSpaceHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} (h : SSet.Homotopy f g) :
    SimplicialObject.Homotopy (linearizedSpaceMap f) (linearizedSpaceMap g) :=
  h.toSimplicialObjectHomotopy.whiskerRight integerLinearization

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
