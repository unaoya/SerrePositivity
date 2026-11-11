module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingEquivalenceClasses
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionPinchedSpaces

/-!
概要：pinched 写像空間の同値からパラメータ付き Hom の対応を取り出す。
方針：右模型と区間模型の比較で共役し、族のホモトピー類を使う。
規約：対象変数の自然性や単位の存在はここでは入力に含めない。
使われ方：写像空間による随伴の特徴づけの逆方向の橋。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：pinched 模型の同値を区間模型の同値へ移す。
方針：始域側の比較の逆、指定同値、終域側の比較を合成する。
規約：二つの周囲の quasicategory は異なってよい。
使われ方：任意の pinched 同値からパラメータ付き Hom 対応を作る。 -/
noncomputable def intervalEquivalenceOfPinched {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x₀ x₁).choose.symm.trans
    (e.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence y₀ y₁).choose)

/-- 概要：pinched 写像空間の同値が誘導する定値関手間 Hom の全単射。
方針：区間模型へ移して、ホモトピー類による表示に作用させる。
規約：任意の単体集合パラメータ A。
使われ方：自然な写像空間対応の二胞体レベルへの表示。 -/
noncomputable def pinchedMappingEquivalenceHomEquiv (A : SSet.{u}) {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x₀ x₁ ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A Y y₀ y₁ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEquivalenceHomEquiv A (intervalEquivalenceOfPinched e)

/-- 概要：pinched 同値に由来する Hom 対応はパラメータに自然。
方針：区間模型の同値についての既存の自然性を使う。
規約：A,B に quasicategory 性は不要。
使われ方：逆方向の対応をパラメータ付きで扱う。 -/
lemma pinchedMappingEquivalenceHomEquiv_precomp {A B X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁))
    (i : A ⟶ B) (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom B X x₀ x₁) :
    pinchedMappingEquivalenceHomEquiv A e (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp i α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp i (pinchedMappingEquivalenceHomEquiv B e α) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEquivalenceHomEquiv_precomp (intervalEquivalenceOfPinched e) i α

/-- 概要：順方向に構成した写像空間の同値から元の adjunct 対応が回収される。
方針：任意の Hom を族で表し、比較射が表す adjunct の公式を使う。
規約：パラメータ A は quasicategory、比較射は既存の intervalMap。
使われ方：写像空間の同値と二胞体の対応の往復の整合。 -/
lemma QCatAdjunction.intervalMappingEquivalence_homEquiv {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEquivalenceHomEquiv A (a.intervalMappingEquivalence x y) =
      a.constantHomEquiv A x y := by
  apply Equiv.ext
  intro α
  obtain ⟨f, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_surjective A Y (F.app (Opposite.op ⦋0⦌) x) y α
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEquivalenceHomEquiv_family]
  exact a.intervalMap_family x y f

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.QCatAdjunction (intervalMappingEquivalence_homEquiv)


/-- 概要：随伴の pinched 同値を区間模型に戻すと元の比較射に同型。
方針：既存の模型比較の正方形と始域側の比較の逆則を合わせる。
規約：同じ比較・逆の選択を用いる。
使われ方：pinched 同値から Hom 対応への橋の順方向との整合。 -/
noncomputable def QCatAdjunction.pinchedEquivalenceIntervalIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (intervalEquivalenceOfPinched (a.pinchedHomEquivalence x y)).hom
      (a.intervalMap x y) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (F.app (Opposite.op ⦋0⦌) x) y).choose
  have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (e.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ≫ a.intervalMap x y))
      (a.intervalMap x y) := by
    simpa only [e, Category.assoc, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.choose] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.invHomIso (a.intervalMap x y)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (a.pinchedMap_comparisonIso x y) e.inv) ≪≫ h₂

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.QCatAdjunction (pinchedEquivalenceIntervalIso)


/-- 概要：随伴の pinched 同値から元の定値関手間 adjunct 対応が回収される。
方針：模型を戻した比較の同型をホモトピーにし、Hom 対応の不変性を使う。
規約：パラメータ A は quasicategory。
使われ方：随伴から写像空間同値、Hom 対応への順方向の往復。 -/
lemma QCatAdjunction.pinchedHomEquivalence_homEquiv {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    pinchedMappingEquivalenceHomEquiv A (a.pinchedHomEquivalence x y) =
      a.constantHomEquiv A x y := by
  unfold pinchedMappingEquivalenceHomEquiv
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEquivalenceHomEquiv_eq_of_homotopy (A := A)
    (intervalEquivalenceOfPinched (a.pinchedHomEquivalence x y))
    (a.intervalMappingEquivalence x y) (a.pinchedEquivalenceIntervalIso x y).simplicialHomotopy
  exact h.trans (a.intervalMappingEquivalence_homEquiv x y)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.QCatAdjunction (pinchedHomEquivalence_homEquiv)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
