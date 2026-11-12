module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismOpposite

/-!
概要：標準単体とその境界をパラメーターとする prism の正規化した反転。
方針：パラメーターの標準反転同型で反転した prism の始域を戻す。
規約：境界包含と可換な反転を取る。
使われ方：Kerodon §7.1.5（Tag 02WE） の終点側の prism の延長。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：標準単体の境界はその反転と同型。
方針：標準単体の反転同型を境界の逆像へ制限する。
規約：元の境界から反転した境界への向き。
使われ方：Kerodon §7.1.5（Tag 02WE） の境界の prism の双対化。 -/
def boundaryReverseIso (n : ℕ) : (boundary n : SSet.{u}) ≅ (boundary n : SSet.{u}).op :=
  Subcomplex.eqToIso (op_boundary n).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso (boundary n).op (stdSimplex.opIso ⦋n⦌).symm ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.subcomplexOppositeIso (boundary n)).symm

/-- 概要：境界の反転同型は包含と可換。
方針：部分複体の逆像の包含を消去する。
規約：周囲では標準単体の反転同型の逆射を使う。
使われ方：Kerodon §7.1.5（Tag 02WE） の相対充填の双対化。 -/
lemma boundaryReverseIso_hom_ι (n : ℕ) :
    (boundaryReverseIso.{u} n).hom ≫ SSet.opFunctor.map (boundary n).ι =
      (boundary n).ι ≫ (stdSimplex.opIso ⦋n⦌).inv := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.subcomplexOppositeIso_hom_ι]
  change ((Subcomplex.homOfLE (op_boundary n).symm.le ≫
    (boundary n).op.fromPreimage (stdSimplex.opIso ⦋n⦌).inv) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.subcomplexOppositeIso (boundary n)).inv) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.subcomplexOppositeIso (boundary n)).hom ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, Category.assoc,
    Subcomplex.fromPreimage_ι, ← Category.assoc, Subcomplex.homOfLE_ι]

/-- 概要：標準単体の prism をパラメーターも反転して同じ標準単体の prism に戻す。
方針：反転したパラメーターへ標準反転同型の逆射で写す。
規約：標的は反転する。
使われ方：Kerodon §7.1.5（Tag 02WE） の始点側と終点側の交換。 -/
def reverseStdPrism {Y : SSet.{u}} {n : ℕ} (H : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Y) :
    (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Y.op :=
  (Δ[1] ◁ (stdSimplex.opIso ⦋n⦌).inv) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism H

/-- 概要：境界の prism をパラメーターも反転して元の境界の prism に戻す。
方針：境界の反転同型でパラメーターを写す。
規約：標的は反転する。
使われ方：Kerodon §7.1.5（Tag 02WE） の指定した境界の双対化。 -/
def reverseBoundaryPrism {Y : SSet.{u}} {n : ℕ}
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ Y) :
    (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ Y.op :=
  (Δ[1] ◁ (boundaryReverseIso n).hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism H

/-- 概要：標準単体の prism の反転は境界への制限と可換。
方針：境界反転の包含との可換性と prism の反転の自然性を使う。
規約：両方のパラメーターは元の標準単体の次数に戻す。
使われ方：Kerodon §7.1.5（Tag 02WE） の境界の延長の回収。 -/
lemma reverseStdPrism_boundary {Y : SSet.{u}} {n : ℕ}
    (H : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Y) :
    (Δ[1] ◁ (boundary n).ι) ≫ reverseStdPrism H =
      reverseBoundaryPrism ((Δ[1] ◁ (boundary n).ι) ≫ H) := by
  unfold reverseStdPrism reverseBoundaryPrism
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_precomp, ← Category.assoc, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
    boundaryReverseIso_hom_ι]

/-- 概要：標準単体の prism の二重反転は元へ戻る。
方針：二つの反転の自然性と標準単体の二重反転を消去する。
規約：標的の二重反転同型を最後に合成する。
使われ方：Kerodon §7.1.5（Tag 02WE） の反転した充填の復帰。 -/
lemma reverseStdPrism_double {Y : SSet.{u}} {n : ℕ}
    (H : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Y) :
    reverseStdPrism (reverseStdPrism H) ≫ (SSet.opFunctorCompOpFunctorIso.app Y).hom = H := by
  unfold reverseStdPrism
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_precomp]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_double]
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.stdSimplex_doubleReverse, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

/-- 概要：境界の反転を二度適用すると元へ戻る。
方針：各単体の値の二重反転を計算する。
規約：境界の二重反転同型を挿入する。
使われ方：Kerodon §7.1.5（Tag 02WE） の境界の双対化の復帰。 -/
lemma boundaryReverseIso_double (n : ℕ) :
    (boundaryReverseIso.{u} n).hom ≫ SSet.opFunctor.map (boundaryReverseIso n).hom ≫
      (SSet.opFunctorCompOpFunctorIso.app (boundary n : SSet.{u})).hom = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  change ((a.val i.rev.rev).rev).rev = a.val i
  simp

/-- 概要：境界の prism の二重反転は元へ戻る。
方針：境界の二重反転と prism の二重反転を消去する。
規約：標的の二重反転同型を合成する。
使われ方：Kerodon §7.1.5（Tag 02WE） の境界を指定した充填の復帰。 -/
lemma reverseBoundaryPrism_double {Y : SSet.{u}} {n : ℕ}
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ Y) :
    reverseBoundaryPrism (reverseBoundaryPrism H) ≫
      (SSet.opFunctorCompOpFunctorIso.app Y).hom = H := by
  unfold reverseBoundaryPrism
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_precomp]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_double]
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc, boundaryReverseIso_double, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

/-- 概要：正規化した標準 prism の反転は端点を交換する。
方針：端点の自然性と prism の反転の端点公式を使う。
規約：パラメーターには標準単体の反転を適用する。
使われ方：Kerodon §7.1.5（Tag 02WE） の終点を固定した延長。 -/
lemma reverseStdPrism_endpoint {Y : SSet.{u}} {n : ℕ}
    (H : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Y) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i Δ[n] ≫ reverseStdPrism H =
      (stdSimplex.opIso ⦋n⦌).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i.rev Δ[n] ≫ H) := by
  unfold reverseStdPrism
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_endpoint]

/-- 概要：正規化した境界の prism の反転は端点を交換する。
方針：端点の自然性と prism の反転の端点公式を使う。
規約：パラメーターには境界の反転を適用する。
使われ方：Kerodon §7.1.5（Tag 02WE） の境界上の終点の固定。 -/
lemma reverseBoundaryPrism_endpoint {Y : SSet.{u}} {n : ℕ}
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ Y) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (boundary n : SSet.{u}) ≫ reverseBoundaryPrism H =
      (boundaryReverseIso n).hom ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i.rev (boundary n : SSet.{u}) ≫ H) := by
  unfold reverseBoundaryPrism
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_endpoint]

/-- 概要：標準 prism の正規化した反転は後合成と可換。
方針：prism の反転の後合成の自然性を使う。
規約：標的の射も反転する。
使われ方：Kerodon §7.1.5（Tag 02WE） の基底上の充填の双対化。 -/
lemma reverseStdPrism_postcomp {Y Z : SSet.{u}} {n : ℕ}
    (H : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Y) (p : Y ⟶ Z) :
    reverseStdPrism (H ≫ p) = reverseStdPrism H ≫ SSet.opFunctor.map p := rfl

/-- 概要：境界の prism の正規化した反転は後合成と可換。
方針：prism の反転の後合成の自然性を使う。
規約：標的の射も反転する。
使われ方：Kerodon §7.1.5（Tag 02WE） の指定された境界の双対化。 -/
lemma reverseBoundaryPrism_postcomp {Y Z : SSet.{u}} {n : ℕ}
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ Y) (p : Y ⟶ Z) :
    reverseBoundaryPrism (H ≫ p) = reverseBoundaryPrism H ≫ SSet.opFunctor.map p := rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
