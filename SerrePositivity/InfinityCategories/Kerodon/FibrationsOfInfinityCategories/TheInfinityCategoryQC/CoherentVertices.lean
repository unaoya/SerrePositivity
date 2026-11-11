module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices

/-!
概要：coherent nerve の零単体と元の単体的圏の対象との往復対応。
方針：定値豊穣関手を構成し、一点 thickening の単位 Hom の同型で逆を検証する。
規約：対象と Hom の宇宙を分け、CatInfinity の既存の定義を再利用する。
使われ方：Kerodon §5.5.3（Tag 0208）、Cat_∞ の対象と小さい quasicategory の同定。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe v u w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：任意の豊穣圏から単体的圏への定値豊穣関手。
方針：各 Hom を単位対象への唯一の射と対象の豊穣単位の合成で送る。
規約：定値な射は指定対象の恒等射であり、合成を厳密に保つ。
使われ方：coherent nerve の零単体と退化単体の構成。 -/
def coherentConstantFunctor (D : Type w) [EnrichedCategory SSet.{v} D] (X : C) :
    EnrichedFunctor SSet D C where
  obj _ := X
  map _ _ := toUnit _ ≫ eId SSet X
  map_id _ := by simp
  map_comp a b c := by
    change eComp SSet a b c ≫ (toUnit _ ≫ eId SSet X) =
      ((toUnit _ ≫ eId SSet X) ⊗ₘ (toUnit _ ≫ eId SSet X)) ≫ eComp SSet X X X
    simp only [comp_toUnit_assoc]
    rw [← tensorHom_comp_tensorHom]
    have hi : (eId SSet X ⊗ₘ eId SSet X) ≫ eComp SSet X X X =
        (λ_ (𝟙_ SSet)).hom ≫ eId SSet X := by
      apply (cancel_epi (λ_ (𝟙_ SSet)).inv).mp
      simpa using (eHomEquiv_comp SSet (𝟙 X) (𝟙 X)).symm
    rw [Category.assoc, hi, ← Category.assoc]
    congr 1

/-- 概要：対象を coherent nerve の頂点として表示する。
方針：一点の simplicial thickening からの定値豊穣関手を使う。
規約：頂点は SimplicialNerve の native な零単体。
使われ方：Cat_∞ の対象の具体的な表示。 -/
def coherentVertex (X : C) : (SimplicialNerve C) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X

/-- 概要：coherent nerve の頂点は唯一の対象での評価から回収できる。
方針：一点 thickening の対象の一意性と、単位 Hom の同型性で比較する。
規約：元の豊穣関手そのものの等式であり、同型による商を取らない。
使われ方：頂点と対象の対応の逆写像の検証。 -/
lemma coherentVertex_recover (F : (SimplicialNerve C) _⦋0⦌) :
    coherentVertex (F.obj ⟨ULift.up 0⟩) = F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object F

/-- 概要：coherent nerve の頂点と元の単体的圏の対象は全単射に対応する。
方針：唯一の対象での評価を逆写像とし、定値関手の回収補題を使う。
規約：一般の単体的圏に適用でき、局所 Kan 性を要求しない。
使われ方：Cat_∞ の頂点の厳密な読み戻し。 -/
def coherentVertexEquiv : C ≃ (SimplicialNerve C) _⦋0⦌ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv C

/-- 概要：Cat_∞ の頂点は小さい quasicategory と同一の情報を持つ。
方針：既存の CatInfinity = SimplicialNerve QCat に頂点の全単射を適用する。
規約：小さい単体は宇宙 u、Cat_∞ の単体は宇宙 u+1。
使われ方：F2-lite の引き戻しを Cat_∞ の対象として表示する。 -/
def catInfinityVertexEquiv : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋0⦌ := coherentVertexEquiv

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
