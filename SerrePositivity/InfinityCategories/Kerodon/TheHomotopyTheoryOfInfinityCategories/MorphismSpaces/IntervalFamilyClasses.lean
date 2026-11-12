module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyInvariance
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantAdjunct

/-!
概要：区間写像空間への族のホモトピー類と定値関手間の h Fun の Hom の全単射。
方針：実際のホモトピーによる関係を、射の等式との同値で同値関係と確認する。
規約：標的は quasicategory、パラメータは任意の単体集合。
使われ方：写像空間対応の逆方向で、ホモトピー同値をパラメータ付き Hom の対応に移す。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：写像空間への族の実際のホモトピーによる同値関係。
方針：h Fun の射の等式と同値であることから三つの関係則を得る。
規約：関係そのものは Nonempty Homotopy。逆向きのホモトピーも存在する。
使われ方：パラメータ付き族のホモトピー類の商。 -/
def intervalFamilyHomotopySetoid (A X : SSet.{u}) [Quasicategory X] (x y : X _⦋0⦌) :
    Setoid (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) where
  r f g := Nonempty (SSet.Homotopy f g)
  iseqv := {
    refl := fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_iff_homotopy.mp rfl
    symm := fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_iff_homotopy.mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_iff_homotopy.mpr h).symm
    trans := fun h k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_iff_homotopy.mp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_iff_homotopy.mpr h).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_iff_homotopy.mpr k)) }

/-- 概要：区間写像空間へのパラメータ族のホモトピー類。
方針：実際の単体的ホモトピーの同値関係による商を取る。
規約：パラメータ A に quasicategory 性は不要。
使われ方：h Fun の定値関手間の Hom の幾何的な表示。 -/
abbrev IntervalFamilyHomotopyClass (A X : SSet.{u}) [Quasicategory X] (x y : X _⦋0⦌) :=
  Quotient (intervalFamilyHomotopySetoid A X x y)

/-- 概要：族のホモトピー類から h Fun の射への写像。
方針：intervalFamilyHom のホモトピー不変性で商へ降ろす。
規約：選択は使わないが、代表辺の表示は既存の noncomputable な定義を使う。
使われ方：ホモトピー類の全単射。 -/
noncomputable def intervalFamilyClassHom (A X : SSet.{u}) [Quasicategory X] (x y : X _⦋0⦌) :
    IntervalFamilyHomotopyClass A X x y → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x y :=
  Quotient.lift _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (fun _ _ ⟨H⟩ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_of_homotopy H)

/-- 概要：ホモトピー類から h Fun の Hom への写像は全単射。
方針：射の等式からホモトピーを回収する単射性と、辺の代表の全射性を使う。
規約：任意のパラメータ A。
使われ方：写像空間の類と二胞体の間の可逆な変換。 -/
lemma intervalFamilyClassHom_bijective (A X : SSet.{u}) [Quasicategory X]
    (x y : X _⦋0⦌) : Function.Bijective (intervalFamilyClassHom A X x y) := by
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro f g h
    exact Quotient.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_iff_homotopy.mp h)
  · intro α
    obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_surjective A X x y α
    exact ⟨Quotient.mk _ f, hf⟩

/-- 概要：族のホモトピー類と定値関手間の h Fun の Hom の全単射。
方針：商に降ろした写像の単射性・全射性をまとめる。
規約：単なる辺の商の表示であり、quasicategory 間の同値と混同しない。
使われ方：パラメータ付き写像空間による随伴の特徴づけの橋。 -/
noncomputable def intervalFamilyHomotopyEquiv (A X : SSet.{u}) [Quasicategory X]
    (x y : X _⦋0⦌) :
    IntervalFamilyHomotopyClass A X x y ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x y :=
  Equiv.ofBijective _ (intervalFamilyClassHom_bijective A X x y)

/-- 概要：全単射は代表族を既存の h Fun の射へ送る。
方針：商の lift の計算則。
規約：同じ代表族 f を使う。
使われ方：全単射のパラメータ自然性の計算。 -/
lemma intervalFamilyHomotopyEquiv_mk {A X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    intervalFamilyHomotopyEquiv A X x y (Quotient.mk _ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom f := rfl

/-- 概要：パラメータの前合成は族のホモトピー類に降りる。
方針：h Fun の表示の自然性と等式からのホモトピー回収を使う。
規約：A,B は任意の単体集合。
使われ方：全単射をパラメータに自然な対応として使う。 -/
noncomputable def intervalFamilyClassPrecomp {A B X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (i : A ⟶ B) :
    IntervalFamilyHomotopyClass B X x y → IntervalFamilyHomotopyClass A X x y :=
  Quotient.map (i ≫ ·) (by
    intro f g h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_iff_homotopy.mp
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_iff_homotopy.mpr h])

/-- 概要：ホモトピー類と h Fun の Hom の全単射はパラメータに自然。
方針：商の代表で既存の族の自然性を使う。
規約：A,B に quasicategory 性は不要。
使われ方：写像空間の対応をパラメータ付き Hom に移す接続。 -/
lemma intervalFamilyHomotopyEquiv_precomp {A B X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (i : A ⟶ B) (c : IntervalFamilyHomotopyClass B X x y) :
    intervalFamilyHomotopyEquiv A X x y (intervalFamilyClassPrecomp i c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp i (intervalFamilyHomotopyEquiv B X x y c) := by
  refine Quotient.inductionOn c ?_
  intro f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp i f

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
