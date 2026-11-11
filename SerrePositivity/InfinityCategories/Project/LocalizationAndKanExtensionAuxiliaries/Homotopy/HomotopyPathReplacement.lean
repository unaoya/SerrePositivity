module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：Kan 複体内のホモトピーから可逆 path 置換への持ち上げを構成する。
方針：全ての辺が可逆なのでホモトピーを可逆 path に curry し、引き戻しに入れる。
規約：比較射の fibration 性は要求しない。
使われ方：comma の正方形から導来 fiber への比較射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy

/-- 概要：Kan 複体内のホモトピーを可逆 path の族にする。
方針：curry した全頂点の辺がホモトピー圏で可逆であることを使う。
規約：始域 A は任意。
使われ方：path 置換への持ち上げの第一成分。 -/
noncomputable def homotopyEquivalencePath {A Y : SSet.{u}} [KanComplex Y]
    {f g : A ⟶ Y} (H : SSet.Homotopy f g) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    (curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h)) (fun _ ↦ by
      change IsIso _
      exact IsGroupoid.all_isIso (C := hoFunctor.obj Y) _)

/-- 概要：ホモトピーの可逆 path の始点は元の始点。
方針：包含の公式と区間の端点評価を使う。
規約：厳密な射の等式。
使われ方：path 置換の引き戻し条件。 -/
lemma homotopyEquivalencePath_zero {A Y : SSet.{u}} [KanComplex Y]
    {f g : A ⟶ Y} (H : SSet.Homotopy f g) :
    homotopyEquivalencePath H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0 = f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint, ← Category.assoc,
    show homotopyEquivalencePath H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y =
      curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h) from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, ← Category.assoc]
  exact H.h₀

/-- 概要：ホモトピーの可逆 path の終点は元の終点。
方針：包含の公式と区間の端点評価を使う。
規約：厳密な射の等式。
使われ方：導来 fiber の指定点の条件。 -/
lemma homotopyEquivalencePath_one {A Y : SSet.{u}} [KanComplex Y]
    {f g : A ⟶ Y} (H : SSet.Homotopy f g) :
    homotopyEquivalencePath H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1 = g := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint, ← Category.assoc,
    show homotopyEquivalencePath H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y =
      curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h) from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, ← Category.assoc]
  exact H.h₁

/-- 概要：q 後の射から b へのホモトピーは q の path 置換への持ち上げを与える。
方針：可逆 path と元の始域の射を引き戻しで組み合わせる。
規約：q に fibration 性を仮定しない。
使われ方：導来 fiber に値を持つ射の構成。 -/
noncomputable def homotopyPathReplacementLift {A X Y : SSet.{u}} [KanComplex Y]
    (q : X ⟶ Y) (a : A ⟶ X) {b : A ⟶ Y} (H : SSet.Homotopy (a ≫ q) b) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement q :=
  pullback.lift (homotopyEquivalencePath H) a (homotopyEquivalencePath_zero H)

/-- 概要：ホモトピーによる path 置換への持ち上げは元の始域の射を保つ。
方針：引き戻しの第二射影。
規約：厳密な射の等式。
使われ方：comma の標的写像空間への射との整合性。 -/
lemma homotopyPathReplacementLift_projection {A X Y : SSet.{u}} [KanComplex Y]
    (q : X ⟶ Y) (a : A ⟶ X) {b : A ⟶ Y} (H : SSet.Homotopy (a ≫ q) b) :
    homotopyPathReplacementLift q a H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection q = a :=
  pullback.lift_snd _ _ _

/-- 概要：ホモトピーによる path 置換への持ち上げの終点は指定された射。
方針：引き戻しの第一射影と path の終点公式。
規約：厳密な射の等式。
使われ方：頂点 fiber への持ち上げ。 -/
lemma homotopyPathReplacementLift_map {A X Y : SSet.{u}} [KanComplex Y]
    (q : X ⟶ Y) (a : A ⟶ X) {b : A ⟶ Y} (H : SSet.Homotopy (a ≫ q) b) :
    homotopyPathReplacementLift q a H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q = b := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap, ← Category.assoc]
  rw [show homotopyPathReplacementLift q a H ≫ pullback.fst _ _ =
    homotopyEquivalencePath H from pullback.lift_fst _ _ _, homotopyEquivalencePath_one]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
