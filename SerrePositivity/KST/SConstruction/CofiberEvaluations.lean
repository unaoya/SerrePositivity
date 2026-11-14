module
public import SerrePositivity.KST.SConstruction.ZeroCofiberExactness

/-! # cofiber 図式の各角の完全な評価
概要：cofiber 図式の包含と各角の評価が零対象と全押し出しを保つ。
方針：S₂ への完全な切断と gapped 包含によって包含の保存を示す。
規約：全零角の cofiber 図式を使う。使われ方：McCarthy の subobject と quotient の射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：安定な標的への関手圏の添字制限は零対象と全押し出しを保つ。
方針：各点での合成が元の関手圏の評価であることを使う。
規約：添字の射は任意。使われ方：cofiber 包含の完全性。 -/
lemma pre_preservesSConstructionData {A B C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (i : A ⟶ B) : PreservesSConstructionData ((pre i).app C) := by
  apply preservesSConstructionData_functor_of_pointwise
  intro a
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  exact evaluateFunctorAt_preservesSConstructionData _

/-- 概要：cofiber 図式の包含は零対象と全押し出しを保つ。
方針：S₂ への切断・gapped 包含・中央正方形への制限の合成として表示する。
規約：零角を一つに固定しない。使われ方：各角の完全な評価。 -/
lemma cofiberInclusion_preservesSConstructionData (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    PreservesSConstructionData
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsCofiberDiagramVertex (C := C))).ι := by
  have h := ((sTwoCofiberSection_preservesSConstructionData C).comp
    (gappedInclusion_preservesSConstructionData 2 C)).comp
      (pre_preservesSConstructionData arTwoMiddleSquare)
  have he : (sTwoCofiberSection C ≫ (gappedSubcomplex 2 C).ι) ≫
      (pre arTwoMiddleSquare).app C =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsCofiberDiagramVertex (C := C))).ι := by
    rw [Category.assoc, ← sTwoCofiberRestriction_ι, ← Category.assoc,
      sTwoCofiberSection_projection, Category.id_comp]
  rwa [he] at h

/-- 概要：cofiber 図式の各角の評価は零対象と全押し出しを保つ。
方針：包含と関手圏の点での評価を合成する。
規約：全ての四角形の頂点を許す。使われ方：McCarthy の三つの対象の射。 -/
lemma cofiberEvaluation_preservesSConstructionData (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (a : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    PreservesSConstructionData
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a) :=
  (cofiberInclusion_preservesSConstructionData C).comp
    (evaluateFunctorAt_preservesSConstructionData a)

/-- 概要：cofiber 図式の各角の評価を安定な入力間の射にする。
方針：零対象と全押し出しの保存から cofiber 保存を取り出す。
規約：底の射は元の評価。使われ方：object S と core S の関手への入力。 -/
def cofiberStableEvaluation (X : StableModel.{u})
    (a : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) : cofiberStableModel X ⟶ X :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a,
    (cofiberEvaluation_preservesSConstructionData X.carrier a).toCofiberData⟩

/-- 概要：cofiber 列の subobject を取る完全関手。
方針：正方形の (0,0) を評価する。
規約：S₂ の中央正方形表示を使う。使われ方：McCarthy の左 fiber の基底。 -/
def cofiberStableSubobject (X : StableModel.{u}) : cofiberStableModel X ⟶ X :=
  cofiberStableEvaluation X (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)

/-- 概要：cofiber 列の middle を取る完全関手。
方針：正方形の (1,0) を評価する。
規約：全 cofiber の選択を保持する。使われ方：McCarthy の押し出しの中間項。 -/
def cofiberStableMiddle (X : StableModel.{u}) : cofiberStableModel X ⟶ X :=
  cofiberStableEvaluation X (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0)

/-- 概要：cofiber 列の quotient を取る完全関手。
方針：正方形の (1,1) を評価する。
規約：型に distinguished triangle の仮定を加えない。使われ方：McCarthy の左 fiber からの射。 -/
def cofiberStableQuotient (X : StableModel.{u}) : cofiberStableModel X ⟶ X :=
  cofiberStableEvaluation X (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)

/-- 概要：標準零 cofiber 関手を安定な入力間の完全関手にする。
方針：既存の零対象と全押し出しの保存を添える。
規約：false は λ、true は ι の cofiber 図式。使われ方：McCarthy の object S の関手。 -/
def zeroCofiberStableFunctor (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex X.carrier) (b : Bool) :
    X ⟶ cofiberStableModel X :=
  ⟨zeroCofiberFunctor z b, (zeroCofiberFunctor_preservesSConstructionData z b).toCofiberData⟩

/-- 概要：標準零 cofiber 関手の subobject は恒等または指定零対象。
方針：正方形の零角の隣の評価の式。
規約：全単体での厳密な等号。使われ方：McCarthy の fiber の基底の照合。 -/
lemma zeroCofiberStableFunctor_subobject (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex X.carrier)
    (b : Bool) : (zeroCofiberStableFunctor X z b).val ≫ (cofiberStableSubobject X).val =
      (if b then SSet.const z.vertex else 𝟙 X.carrier) := by
  change zeroCofiberFunctor z b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) = _
  rw [← Category.assoc, zeroCofiberFunctor_ι, zeroCofiberSquare_evaluation]
  cases b <;> simp

/-- 概要：ι 型の標準零 cofiber 関手の商は完全関手として恒等射。
方針：商の厳密な評価公式を部分型の外延性で移す。
規約：保存条件の証明の選択によらない。使われ方：McCarthy の fiber の射の厳密な切断。 -/
lemma zeroCofiberStableFunctor_quotient (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex X.carrier) :
    zeroCofiberStableFunctor X z true ≫ cofiberStableQuotient X = 𝟙 X :=
  Subtype.ext (zeroCofiberFunctor_quotient z true)

end SerrePositivity.KST.SConstruction
