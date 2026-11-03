module
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-! # 複体同型の逆射を元の斉次元で評価する
概要：順射による斉次元の回収式から、同じ逆射の値を計算する。
方針：抽象的な複体のまま逆律を評価し、大きい具体的複体の展開を避ける。
規約：検証上限を変更しない。使われ方：実 tensor 単位の逆と合成比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] {X Y : Complex A}

/-- 順方向の元の回収式は、同じ複体同型の逆方向の回収式を与える。 -/
lemma dgComplexIso_inv_apply_eq (e : X ≅ Y) (n : ℤ) (x : X.X n) (y : Y.X n)
    (h : e.hom.f n x = y) : e.inv.f n y = x := by
  have hi := chain_comp_apply_of_eq e.hom e.inv (𝟙 X) e.hom_inv_id n x
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply] at hi
  have ht := congrArg (fun z => e.inv.f n z) h
  exact ht.symm.trans hi

/-- 逆射で前合成して恒等射となる射は、同じ元の同型の順射である。 -/
lemma dgComplexIso_hom_eq_of_inv_comp (e : X ≅ Y) (f : X ⟶ Y)
    (h : e.inv ≫ f = 𝟙 Y) : f = e.hom := by
  calc
    f = (e.hom ≫ e.inv) ≫ f := by rw [Iso.hom_inv_id, Category.id_comp]
    _ = e.hom := by rw [Category.assoc, h, Category.comp_id]

/-- 抽象的な複体の射による斉次元の等号の移送。 -/
lemma dgComplexMap_apply_congr {Z : Complex A} (f : X ⟶ Z) (n : ℤ)
    {x y : X.X n} (h : x = y) : f.f n x = f.f n y :=
  congrArg (fun t => f.f n t) h

/-- 三つの射の合成を、抽象複体のまま斉次元で評価する。 -/
lemma dgComplexMap_triple_apply {Z W : Complex A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (n : ℤ) (x : X.X n) :
    (f ≫ g ≫ h).f n x = h.f n (g.f n (f.f n x)) := rfl

/-- 恒等 chain map は、同じ元を回収する。 -/
lemma dgComplexMap_identity_apply (V : Complex A) (n : ℤ) (x : V.X n) :
    (𝟙 V : V ⟶ V).f n x = x := rfl

end SerrePositivity.KST.SConstruction
