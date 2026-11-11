module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite

/-!
概要：区間を持つ prism の反転。
方針：区間の順序反転と単体集合の op を組み合わせる。
規約：パラメーターも反転し、区間の両端を交換する。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の終点側の持ち上げ。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：反転は二つの単体集合の直積と可換。
方針：各次数で組の恒等同型を使う。
規約：テンソル積は単体集合の直積。
使われ方：Kerodon §4.5.3（Tag 032Y） の prism の双対化。 -/
def opTensorIso (A B : SSet.{u}) : A.op ⊗ B.op ≅ (A ⊗ B).op :=
  NatIso.ofComponents (fun _ ↦ (Equiv.refl _).toIso) (fun _ ↦ by rfl)

/-- 概要：prism を区間とパラメーターの両方について反転する。
方針：区間の反転同型と直積の反転同型で前合成する。
規約：標的も反転する。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の両端の交換。 -/
def reversePrism {A Y : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) :
    (Δ[1] : SSet.{u}) ⊗ A.op ⟶ Y.op :=
  ((stdSimplex.opIso ⦋1⦌).inv ▷ A.op) ≫ (opTensorIso Δ[1] A).hom ≫ SSet.opFunctor.map H

/-- 概要：prism の反転はパラメーター上の前合成と可換。
方針：各次数の組を計算する。
規約：パラメーターの射も反転する。
使われ方：Kerodon §4.5.3（Tag 032Y） の制限の双対化。 -/
lemma reversePrism_precomp {A B Y : SSet.{u}} (i : A ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ Y) :
    reversePrism ((Δ[1] ◁ i) ≫ H) = (Δ[1] ◁ SSet.opFunctor.map i) ≫ reversePrism H := rfl

/-- 概要：prism の反転は標的上の後合成と可換。
方針：opFunctor の合成保存を使う。
規約：標的の射は任意。
使われ方：Kerodon §4.5.3（Tag 032Y） の反転からの復帰。 -/
lemma reversePrism_postcomp {A Y Z : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (p : Y ⟶ Z) : reversePrism (H ≫ p) = reversePrism H ≫ SSet.opFunctor.map p := rfl

/-- 概要：prism の反転は区間の両端を交換する。
方針：定値の区間単体を反転する。
規約：端点の添字は Fin 2。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の終点の固定。 -/
lemma reversePrism_endpoint {A Y : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (i : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A.op ≫ reversePrism H =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i.rev A ≫ H) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  congr 1

/-- 概要：prism の反転を二度適用すると元へ戻る。
方針：有限順序集合の添字と値の二重反転を計算する。
規約：パラメーターと標的の二重反転同型を挿入する。
使われ方：Kerodon §4.5.3（Tag 032Y） の双対化した延長の回収。 -/
lemma reversePrism_double {A Y : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) :
    reversePrism (reversePrism H) ≫ (SSet.opFunctorCompOpFunctorIso.app Y).hom =
      (Δ[1] ◁ (SSet.opFunctorCompOpFunctorIso.app A).hom) ≫ H := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, a⟩
  change H.app _ (_, _) = H.app _ (t, _)
  congr 2
  apply stdSimplex.ext
  intro i
  change ((t i.rev.rev).rev).rev = t i
  simp

/-- 概要：prism の可逆な垂直辺は反転後も可逆。
方針：反転後の垂直辺が元の辺の op であることを計算する。
規約：標的の quasicategory 性を仮定する。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の双対化。 -/
lemma reversePrism_vertical_isInvertible {A Y : SSet.{u}} [Quasicategory Y]
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (hH : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))))
    (x : A.op _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((reversePrism H).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.IsInvertibleEdge.op (hH (SSet.opObjEquiv x))
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SSet.opObjEquiv x) 1)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((reversePrism H).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))).edge := by
    change SSet.opObjEquiv.symm (H.app (Opposite.op ⦋1⦌) (_, _)) =
      SSet.opObjEquiv.symm (H.app (Opposite.op ⦋1⦌) (_, _))
    congr 2
    apply Prod.ext
    · apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    · rfl
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mp h

/-- 概要：反転した prism を元のパラメーターと標的へ戻す。
方針：区間を再反転し、二重反転の自然同型を挿入する。
規約：始域は元の A、標的は元の Y。
使われ方：Kerodon §4.5.3（Tag 032Y） の双対化した延長の回収。 -/
def unreversePrism {A Y : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ A.op ⟶ Y.op) :
    (Δ[1] : SSet.{u}) ⊗ A ⟶ Y :=
  (Δ[1] ◁ (SSet.opFunctorCompOpFunctorIso.app A).inv) ≫
    reversePrism H ≫ (SSet.opFunctorCompOpFunctorIso.app Y).hom

/-- 概要：prism の反転を戻す操作は反転の左逆。
方針：二重反転の計算とパラメーター同型の逆関係を使う。
規約：対象に quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y） の制限の回収。 -/
lemma unreversePrism_reversePrism {A Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) : unreversePrism (reversePrism H) = H := by
  unfold unreversePrism
  rw [reversePrism_double]
  simp

/-- 概要：反転から戻す操作はパラメーター上の前合成と可換。
方針：二重反転の自然性を成分ごとに計算する。
規約：元の射の op で前合成する。
使われ方：Kerodon §4.5.3（Tag 032Y） の部分複体上の制限。 -/
lemma unreversePrism_precomp {A B Y : SSet.{u}} (i : A ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ B.op ⟶ Y.op) :
    unreversePrism ((Δ[1] ◁ SSet.opFunctor.map i) ≫ H) =
      (Δ[1] ◁ i) ≫ unreversePrism H := rfl

/-- 概要：反転から戻した prism の終点は反転前の始点。
方針：定値の区間単体を計算する。
規約：二重反転の自然同型でパラメーターと標的を戻す。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の終点の回収。 -/
lemma unreversePrism_endpoint {A Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A.op ⟶ Y.op) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A ≫ unreversePrism H =
      (SSet.opFunctorCompOpFunctorIso.app A).inv ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i.rev A.op ≫ H) ≫
          (SSet.opFunctorCompOpFunctorIso.app Y).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  congr 1

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
