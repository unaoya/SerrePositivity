module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：内部 Hom の単体の宇宙持ち上げとその逆。
方針：各パラメーターで入力の ULift を外して評価し、出力を ULift する。
規約：標準単体の添字の圏は変えず、値の宇宙だけを持ち上げる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元の相対写像空間と coherent な復元の宇宙を揃える。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：内部 Hom の単体を宇宙持ち上げした始域・標的の内部 Hom の単体へ移す。
方針：各次数の入力を下ろし、元の評価の出力を持ち上げる。
規約：内部 Hom のパラメーターの単体は同じ添字を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の宇宙移送の順方向。 -/
def uliftFunctorHomUp {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom A).obj E).obj n) :
    ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E)).obj n where
  app d α := ↾fun x => ULift.up (f.app d α x.down)
  naturality g α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact ConcreteCategory.congr_hom (f.naturality g α) x.down

/-- 概要：持ち上げた始域・標的の内部 Hom の単体を元の内部 Hom の単体へ戻す。
方針：入力を持ち上げて評価し、出力の ULift を外す。
規約：追加の宇宙 v は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の宇宙移送の逆方向。 -/
def uliftFunctorHomDown {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj
      ((SSet.uliftFunctor.{v, u}).obj E)).obj n) : ((ihom A).obj E).obj n where
  app d α := ↾fun x => (f.app d α (ULift.up x)).down
  naturality {c d} g α := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun (k : ((SSet.uliftFunctor.{v, u}).obj A).obj c ⟶
      ((SSet.uliftFunctor.{v, u}).obj E).obj d) => (k (ULift.up.{v, u} x)).down)
        (f.naturality g α)

/-- 概要：内部 Hom の単体を持ち上げて下ろすと元に戻る。
方針：各パラメーターで ULift の往復を計算する。
規約：すべての次数での等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の宇宙移送の片側の逆条件。 -/
lemma uliftFunctorHomDown_up {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom A).obj E).obj n) :
    uliftFunctorHomDown (uliftFunctorHomUp.{u, v} f) = f := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 概要：持ち上げた内部 Hom の単体を下ろして再び持ち上げると元に戻る。
方針：各入力の ULift の往復を計算する。
規約：持ち上げた宇宙のすべての内部 Hom の単体を扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の宇宙移送の他方の逆条件。 -/
lemma uliftFunctorHomUp_down {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj
      ((SSet.uliftFunctor.{v, u}).obj E)).obj n) :
    uliftFunctorHomUp (uliftFunctorHomDown f) = f := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 概要：内部 Hom の単体の持ち上げは単射。
方針：下ろす操作が左逆であることを使う。
規約：単体の次数は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の固定条件を元の宇宙へ戻す。 -/
lemma uliftFunctorHomUp_injective {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ} :
    Function.Injective (uliftFunctorHomUp.{u, v} (A := A) (E := E) (n := n)) := by
  intro f g h
  have hh := congrArg (uliftFunctorHomDown.{u, v}) h
  simpa only [uliftFunctorHomDown_up] using hh

/-- 概要：内部 Hom の単体の持ち上げは後合成と可換。
方針：各パラメーターで出力の持ち上げと後合成を計算する。
規約：後合成する射 p の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の底への合成条件の移送。 -/
lemma uliftFunctorHomUp_post {A E B : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (p : E ⟶ B) (f : ((ihom A).obj E).obj n) :
    uliftFunctorHomUp.{u, v} (((ihom A).map p).app n f) =
      ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).map ((SSet.uliftFunctor.{v, u}).map p)).app n
        (uliftFunctorHomUp.{u, v} f) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 概要：関手頂点の定値単体の持ち上げは、持ち上げた関手頂点の定値単体となる。
方針：各次数の評価を計算する。
規約：定値単体の次数 n は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間で固定する底の図式の移送。 -/
lemma uliftFunctorHomUp_constant {A E : SSet.{u}} (a : A ⟶ E) (n : ℕ) :
    uliftFunctorHomUp.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{v, u}).map a)) n := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 概要：内部 Hom の宇宙持ち上げを、持ち上げた対象間の内部 Hom へ写す単体集合の射。
方針：各次数で内部 Hom の単体を持ち上げる。
規約：単体演算は内部 Hom のパラメーターの制限だけを変える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、関手空間の宇宙移送の順方向。 -/
def uliftFunctorSpaceMap (A E : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom A).obj E) ⟶
      (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E) where
  app n := ↾fun f => uliftFunctorHomUp f.down
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply CategoryTheory.Functor.functorHom_ext
    intro k γ
    rfl

/-- 概要：持ち上げた対象間の内部 Hom を、元の内部 Hom の宇宙持ち上げへ戻す射。
方針：各次数で内部 Hom の単体を下ろす。
規約：射の値を ULift して持ち上げた単体集合へ入れる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、関手空間の宇宙移送の逆方向。 -/
def uliftFunctorSpaceDown (A E : SSet.{u}) :
    (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E) ⟶
      (SSet.uliftFunctor.{v, u}).obj ((ihom A).obj E) where
  app n := ↾fun f => ULift.up (uliftFunctorHomDown f)
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    apply CategoryTheory.Functor.functorHom_ext
    intro k γ
    rfl

/-- 概要：内部 Hom の宇宙持ち上げは、持ち上げた対象間の内部 Hom と同型。
方針：内部 Hom の単体の持ち上げと逆方向の往復を各次数で使う。
規約：単体集合の同型であり、単なる同値には弱めない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対写像空間の宇宙の調整。 -/
def uliftFunctorSpaceIso (A E : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom A).obj E) ≅
      (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E) where
  hom := uliftFunctorSpaceMap A E
  inv := uliftFunctorSpaceDown A E
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    exact uliftFunctorHomDown_up.{u, v} f.down
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    exact uliftFunctorHomUp_down.{u, v} f

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
