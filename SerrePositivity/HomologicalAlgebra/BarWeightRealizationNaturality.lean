module

public import SerrePositivity.HomologicalAlgebra.BarWeightEvaluationIso
import all SerrePositivity.HomologicalAlgebra.BarWeightEvaluationIso
import all SerrePositivity.HomologicalAlgebra.BarWeightEvaluation
import all SerrePositivity.HomologicalAlgebra.LinearWeightGenerators
import all SerrePositivity.HomologicalAlgebra.UnderNerveWeight
import all SerrePositivity.HomologicalAlgebra.UnderChainEquiv
import all SerrePositivity.HomologicalAlgebra.SimplicialReplacement

/-!
# bar 重みの coend と単体的置換の全単体作用素の照合

## 概要
各次数の指定同型を、面と退化を含む全単体作用素に自然な同型にまとめる。

## 方針
標準持ち上げを制限したときの先頭の構造射を明示し、同じ coend の関係式を使う。

## 規約
逆射は元の標準持ち上げの生成元であり、単体次数ごとに選び直さない。

## 使われ方
HA 1.2.4。bar の線形 coend の全複体と単体的置換の全複体の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

local instance : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- 全単体作用素による標準持ち上げの制限は、先頭への同じ射による前合成。 -/
theorem underScaffold_restrict {n m : SimplexCategoryᵒᵖ} (r : n ⟶ m)
    (s : ComposableArrows J n.unop.len) :
    underScaffold ((nerve J).map r s) ⋙
        Under.map (s.map (homOfLE (Fin.zero_le (r.unop.toOrderHom 0)))) =
      (nerve (Under (s.obj 0))).map r (underScaffold s) := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · change Under.mk (s.map _ ≫ (𝟙 _ ≫ s.map _)) = Under.mk (𝟙 _ ≫ s.map _)
    rw [Category.id_comp, Category.id_comp, ← s.map_comp]
    rfl
  · intro i j f
    apply (Under.forget (s.obj 0)).map_injective
    simp
    rfl

/-- 重みの単体作用素に関する、指定した生成元の同じ像。 -/
@[reassoc]
theorem barWeightGenerator_map (X : J ⥤ Complex A) {n m : SimplexCategoryᵒᵖ} (r : n ⟶ m)
    (i : J) (τ : ComposableArrows (Under i) n.unop.len) :
    barWeightGenerator A X n i τ ≫ (linearWeightRealization A X).map
        ((coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).map r) =
      barWeightGenerator A X m i ((nerve (Under i)).map r τ) := by
  dsimp only [barWeightGenerator]
  rw [linearWeightGenerator_map]
  congr 1
  simp [coefficientBarWeightι, coefficientBarWeight, underNerveWeight, copowerFunctor]
  rfl

/-- 同じ指定逆射は面・退化を含む全単体作用素に自然。 -/
theorem barWeightEvaluationInv_naturality (X : J ⥤ Complex A)
    {n m : SimplexCategoryᵒᵖ} (r : n ⟶ m) :
    (simplicialReplacement X).map r ≫ barWeightEvaluationInv A X m =
      barWeightEvaluationInv A X n ≫ (linearWeightRealization A X).map
        ((coefficientBarWeight J (𝟙_ (ModuleCat.{u} A))).map r) := by
  apply Sigma.hom_ext
  intro s
  change Sigma.ι (replacementTerms X n) s ≫ replacementMap X r ≫ _ = _
  rw [ι_replacementMap_assoc, ι_barWeightEvaluationInv, ι_barWeightEvaluationInv_assoc,
    barWeightGenerator_map]
  change X.map (s.map (homOfLE (Fin.zero_le (r.unop.toOrderHom 0)))) ≫
    barWeightGenerator A X m (s.obj (r.unop.toOrderHom 0))
      (underScaffold ((nerve J).map r s)) = _
  rw [barWeightGenerator_relation, underScaffold_restrict]

/-- 元の射列・全単体作用素を保つ、bar の coend と単体的置換の指定自然同型。 -/
def barWeightRealizationIso (X : J ⥤ Complex A) :
    coefficientBarWeight J (𝟙_ (ModuleCat.{u} A)) ⋙ linearWeightRealization A X ≅
      simplicialReplacement X := by
  let e : simplicialReplacement X ≅
      coefficientBarWeight J (𝟙_ (ModuleCat.{u} A)) ⋙ linearWeightRealization A X :=
    NatIso.ofComponents (fun n => (barWeightEvaluationIso A X n).symm)
      (fun r => barWeightEvaluationInv_naturality A X r)
  exact e.symm

end SerrePositivity.HomologicalAlgebra
